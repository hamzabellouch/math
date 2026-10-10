import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ForestTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma _root_.OAI.OrderedFinpartition.sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑i,c.partSize i=n := by
  simpa using Fintype.card_congr c.equivSigma

lemma _root_.OAI.OrderedFinpartition.unique_of_partSize_eq {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (hi : c.partSize i=n) (j : Fin c.length) : j=i := by
  by_contra hji
  have hs := Finset.sum_erase_add Finset.univ (fun k => c.partSize k) (Finset.mem_univ i)
  rw [_root_.OAI.OrderedFinpartition.sum_partSize c,hi] at hs
  have hz : ∑k∈Finset.univ.erase i,c.partSize k=0 := by omega
  have hh := Finset.single_le_sum (fun k (_ : k∈Finset.univ.erase i) => Nat.zero_le (c.partSize k))
    (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
  rw [hz] at hh
  have := c.partSize_pos j
  omega

lemma _root_.OAI.OrderedFinpartition.length_eq_one_of_partSize_eq {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (hi : c.partSize i=n) : c.length=1 := by
  have hp : 0<c.length := Nat.zero_lt_of_lt i.isLt
  have hle : c.length≤1 := by
    by_contra h
    have hgt : 1<c.length := by omega
    have he := (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi ⟨0,hp⟩).trans
      (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi ⟨1,hgt⟩).symm
    have hh := congrArg Fin.val he
    change (0:ℕ)=1 at hh
    omega
  omega

lemma partition_majorant_linear {n : ℕ} {M B N : ℕ → ℝ} {z : ℝ}
    (hM : ∀k,0≤M k) (hB : ∀k,0≤B k) (hz : 0≤z)
    (hN : ∀k<n,N k=B k) (hNz : N n=z) :
    (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i))≤
      (Fintype.card (OrderedFinpartition n):ℝ)*M 1*z+
        ∑c : OrderedFinpartition n,M c.length*∏i,B (c.partSize i) := by
  have hb (c : OrderedFinpartition n) : M c.length*(∏i,N (c.partSize i))≤
      M 1*z+M c.length*∏i,B (c.partSize i) := by
    by_cases hh : ∃i,c.partSize i=n
    · obtain ⟨i,hi⟩ := hh
      have hp : (∏j,N (c.partSize j))=z := by
        rw [Finset.prod_eq_single i]
        · rw [hi,hNz]
        · intro j _ hji
          exact (hji (_root_.OAI.OrderedFinpartition.unique_of_partSize_eq c i hi j)).elim
        · simp
      have hMl : M c.length=M 1 := congrArg M (_root_.OAI.OrderedFinpartition.length_eq_one_of_partSize_eq c i hi)
      rw [hp,hMl]
      exact le_add_of_nonneg_right (mul_nonneg (hM 1) (Finset.prod_nonneg (fun j _ => hB _)))
    · have hp : (∏i,N (c.partSize i))=∏i,B (c.partSize i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hN _ (lt_of_le_of_ne (c.partSize_le i) (fun he => hh ⟨i,he⟩))
      rw [hp]
      exact le_add_of_nonneg_left (mul_nonneg (hM 1) hz)
  calc
    _ ≤ ∑c : OrderedFinpartition n,(M 1*z+M c.length*∏i,B (c.partSize i)) :=
      Finset.sum_le_sum (fun c _ => hb c)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_assoc]
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open Set Function
open scoped BigOperators Classical Matrix.Norms.L2Operator

universe u
variable {S : Type u} [Fintype S] {d : ℕ}

abbrev SplitBundle (S : Type u) [Fintype S] (d : ℕ) :=
  ∀p : ProperSplit S, Matrix (OutSlots p → Fin d) (InSlots p → Fin d) ℝ

def splitBundleLinear : ((S → Fin d) → ℝ) →ₗ[ℝ] SplitBundle S d where
  toFun T p := splitMatrix T p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def splitBundle : ((S → Fin d) → ℝ) →L[ℝ] SplitBundle S d :=
  splitBundleLinear.toContinuousLinearMap

lemma allSplitBound_bundle (T : (S → Fin d) → ℝ) :
    AllSplitBound T ‖splitBundle T‖ := by
  intro I O _ _ _ _ _ _ e
  have h := (bound_norm (splitMatrix T (properOfEquiv e))).mono
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (splitBundle T) (properOfEquiv e)) 2)
  have h' := h.reindex (Equiv.arrowCongr (rightOfEquiv e) (Equiv.refl (Fin d)))
    (Equiv.arrowCongr (leftOfEquiv e) (Equiv.refl (Fin d)))
  convert h' using 1
  ext o i
  unfold splitMatrix
  congr 1
  funext s
  rw [splitEquiv_ofEquiv]
  cases e s <;> simp

lemma bundle_norm_le {T : (S → Fin d) → ℝ} {M : ℝ}
    (hM : 0≤M) (h : AllSplitBound T M) : ‖splitBundle T‖≤M := by
  have hp (p : ProperSplit S) : ‖splitMatrix T p‖≤M := by
    have hh : Bound (splitMatrix T p) (M^2) := h (InSlots p) (OutSlots p) (splitEquiv p)
    exact @Bound.norm_le (OutSlots p → Fin d) (InSlots p → Fin d) _ _ (splitMatrix T p) M hM hh
  exact (pi_norm_le_iff_of_nonneg hM).mpr hp

theorem allSplit_gronwall {T D : ℝ → (S → Fin d) → ℝ} {a b δ K ε : ℝ}
    (hc : ContinuousOn T (Icc a b))
    (hd : ∀t∈Ico a b,HasDerivWithinAt T (D t) (Ici t) t)
    (hδ : 0≤δ) (hε : 0≤ε) (hK : 0≤K)
    (hinit : AllSplitBound (T a) δ)
    (hbound : ∀t∈Ico a b,AllSplitBound (D t) (K*‖splitBundle (T t)‖+ε))
    {t : ℝ} (ht : t∈Icc a b) :
    AllSplitBound (T t) (gronwallBound δ K ε (t-a)) := by
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le
    (splitBundle.continuous.comp_continuousOn hc)
    (fun u hu => splitBundle.hasFDerivAt.comp_hasDerivWithinAt u (hd u hu))
    (bundle_norm_le hδ hinit)
    (fun u hu => bundle_norm_le (by positivity) (hbound u hu)) t ht
  exact (allSplitBound_bundle (T t)).mono
    (norm_nonneg _) hb
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma _root_.OAI.OrderedFinpartition.sum_pred_partSize {n : ℕ} (c : OrderedFinpartition n) :
    (∑i,(c.partSize i-1))+c.length=n := by
  have he : (∑i,(c.partSize i-1))+(∑_i : Fin c.length,1)=∑i,c.partSize i := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    _root_.OAI.OrderedFinpartition.sum_partSize c] using he

lemma partition_scale {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n)
    (A B : ℕ → ℝ) (R : ℝ) :
    (A c.length/R^(c.length-1))*(∏i,B (c.partSize i)/R^(c.partSize i-1))=
      (A c.length*(∏i,B (c.partSize i)))/R^(n-1) := by
  rw [Finset.prod_div_distrib,←mul_div_mul_comm,Finset.prod_pow_eq_pow_sum,←pow_add]
  have he : c.length-1+(∑i,(c.partSize i-1))=n-1 := by
    have := _root_.OAI.OrderedFinpartition.sum_pred_partSize c
    have := c.length_pos hn
    omega
  rw [he]

lemma partition_sum_scale {n : ℕ} (hn : 0<n) (A B : ℕ → ℝ) (R : ℝ) :
    (∑c : OrderedFinpartition n,(A c.length/R^(c.length-1))*(∏i,B (c.partSize i)/R^(c.partSize i-1)))=
      (∑c : OrderedFinpartition n,A c.length*(∏i,B (c.partSize i)))/R^(n-1) := by
  simp only [partition_scale hn,Finset.sum_div]

lemma gronwallBound_div (δ K ε t q : ℝ) :
    gronwallBound (δ/q) K (ε/q) t=gronwallBound δ K ε t/q := by
  by_cases hK : K=0
  · simp only [hK,gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK]; ring
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma partition_array_scale {n : ℕ} (c : OrderedFinpartition n)
    (A B : ℕ → ℝ) (R : ℝ) (w : ℕ) :
    (A c.length/R^(c.length+w))*(∏i,B (c.partSize i)/R^(c.partSize i-1))=
      (A c.length*(∏i,B (c.partSize i)))/R^(n+w) := by
  rw [Finset.prod_div_distrib,←mul_div_mul_comm,Finset.prod_pow_eq_pow_sum,←pow_add]
  have he : c.length+w+(∑i,(c.partSize i-1))=n+w := by
    have := _root_.OAI.OrderedFinpartition.sum_pred_partSize c
    omega
  rw [he]

lemma array_composition_scale {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    {f : Point d → Point d} {g : Point d → (S → Fin d) → ℝ} (x : Point d)
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k)
    (R : ℝ) (hR : 0<R) (w : ℕ)
    (hG : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g (f x))) (A k/R^(k+w)))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (B k/R^(k-1))) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      ((∑c : OrderedFinpartition n,A c.length*∏i,B (c.partSize i))/R^(n+w)) := by
  have hh := iteratedFDeriv_array_comp_allSplit x
    (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (hg.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))
    (fun k => A k/R^(k+w)) (fun k => B k/R^(k-1))
    (fun k => div_nonneg (hA _) (pow_nonneg hR.le _))
    (fun k => div_nonneg (hB _) (pow_nonneg hR.le _)) hG hF
  simpa only [partition_array_scale,Finset.sum_div] using hh
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma time_deriv_spatial_jet {ι : Type*} {A : ℝ × E → ℝ}
    (hA : ContDiff ℝ (⊤:ℕ∞) A) (v : ι → E) (l : List ι) (t : ℝ) (y : E) :
    HasDerivAt (fun u => jet v l (fun z => A (u,z)) y)
      (jet v l (fun z => dir (1,0) A (t,z)) y) t := by
  let J := jet (fun i => (0,v i)) l A
  have hJ := smooth_jet hA (fun i => (0,v i)) l
  have he : (fun u => jet v l (fun z => A (u,z)) y)=fun u => J (u,y) := by
    funext u
    exact congrFun (jet_right_slice_at (fun z => hA.contDiffAt) v l) y
  rw [he]
  have hj := ((hJ.differentiable (by simp) (t,y)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hd : jet v l (fun z => dir (1,0) A (t,z)) y=dir (1,0) J (t,y) := by
    rw [jet_right_slice_at (fun z => (smooth_dir hA (1,0)).contDiffAt),jet_dir hA]
  exact hd.symm ▸ hj
end JetCalculus

lemma multilinearTensor_iterated_eq_jet {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) (c : Unit ⊕ Fin n → Fin d) :
    TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n f y) c=
      JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ()))) (f z)) y := by
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  change _=JetCalculus.jet _ _ (L ∘ f) y
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hf),
    L.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,L,
    innerSL_apply_apply,TensorEnergy.multilinearTensor]

lemma spatialTensor_time_deriv {d n : ℕ} {X : ℝ × Point d → Point d}
    (hX : ContDiff ℝ (⊤:ℕ∞) X) (V : Point d → Point d) (t : ℝ)
    (hODE : ∀y,HasDerivAt (fun u => X (u,y)) (V (X (t,y))) t) (y : Point d) :
    HasDerivAt
      (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y))
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => V (X (t,z))) y)) t := by
  apply hasDerivAt_pi.mpr
  intro c
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  let A := L ∘ X
  have hA : ContDiff ℝ (⊤:ℕ∞) A := L.contDiff.comp hX
  have hslice (u : ℝ) : ContDiff ℝ (⊤:ℕ∞) (fun z => X (u,z)) :=
    hX.comp (contDiff_const.prodMk contDiff_id)
  have hd := JetCalculus.time_deriv_spatial_jet hA
    (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))) (List.finRange n) t y
  have he : (fun z => JetCalculus.dir (1,0) A (t,z))=fun z => L (V (X (t,z))) := by
    funext z
    have hleft := ((hA.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    exact hleft.unique (L.hasFDerivAt.comp_hasDerivAt t (hODE z))
  rw [he] at hd
  have hm : ContDiff ℝ (⊤:ℕ∞) (fun z => L (V (X (t,z)))) := by
    rw [←he]
    exact (JetCalculus.smooth_dir hA (1,0)).comp (contDiff_const.prodMk contDiff_id)
  have hf : (fun u => TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (fun z => X (u,z)) y) c)=
      fun u => JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
        (List.finRange n) (fun z => L (X (u,z))) y := by
    funext u
    exact multilinearTensor_iterated_eq_jet (hslice u) y c
  rw [hf]

  have hV : ContDiff ℝ (⊤:ℕ∞) (fun z => V (X (t,z))) := by
    have heV : (fun z => V (X (t,z)))=fun z => (fderiv ℝ X (t,z)) (1,0) := by
      funext z
      exact (hODE z).unique (((hX.differentiable (by simp) (t,z)).hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t z)))
    rw [heV]
    exact ((hX.fderiv_right (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  rw [multilinearTensor_iterated_eq_jet hV]
  exact hd
end LogConcaveSampling

end

end

end

end OAI
