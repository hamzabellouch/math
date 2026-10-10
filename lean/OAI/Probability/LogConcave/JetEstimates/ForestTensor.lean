import Mathlib
import OAI.Probability.LogConcave.Sampling.SpatialTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

lemma AllSplitBound.singleContract_frobenius {d : ℕ} {S T : Type}
    [Fintype S] [Nonempty S] [Fintype T]
    {A : (S ⊕ Unit → Fin d) → ℝ} {M : ℝ}
    (hA : AllSplitBound A M) (B : (T ⊕ Unit → Fin d) → ℝ) :
    (∑c,(TensorEnergy.singleContract A B c)^2)≤M^2*(∑c,(B c)^2) := by
  have ha : Bound (fun (s : S → Fin d) (z : Fin d) => A (Sum.elim s (fun _ => z))) (M^2) := by
    convert (hA Unit S (Equiv.sumComm S Unit)).reindex
      (Equiv.refl (S → Fin d)) (Equiv.funUnique Unit (Fin d)).symm using 1
    funext s z
    congr 1
    funext t
    cases t <;> rfl
  have he (t : T → Fin d) :
      (∑s : S → Fin d,(∑z : Fin d,A (Sum.elim s (fun _ => z))*B (Sum.elim t (fun _ => z)))^2)≤
        M^2*∑z : Fin d,(B (Sum.elim t (fun _ => z)))^2 := ha (fun z => B (Sum.elim t (fun _ => z)))
  have hu := Equiv.sum_comp (Equiv.sumArrowEquivProdArrow S T (Fin d)).symm
    (fun c => (TensorEnergy.singleContract A B c)^2)
  rw [Fintype.sum_prod_type] at hu
  rw [←hu,Finset.sum_comm]
  have hb := Equiv.sum_comp (appendCoordinate (d:=d) T) (fun c => (B c)^2)
  rw [Fintype.sum_prod_type] at hb
  rw [←hb,Finset.mul_sum]
  exact Finset.sum_le_sum (fun t _ => he t)

end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators

def forestTensor {d n : ℕ} {S : Type} (P : Fin n → Type) [∀i,Fintype (P i)]
    (A : (S ⊕ Fin n → Fin d) → ℝ)
    (B : ∀i,(P i ⊕ Unit → Fin d) → ℝ) (c : S ⊕ (Σi,P i) → Fin d) : ℝ :=
  ∑a : Fin n → Fin d,A (Sum.elim (fun s => c (Sum.inl s)) a) *
    ∏i,B i (Sum.elim (fun p => c (Sum.inr ⟨i,p⟩)) (fun _ => a i))

def forestRoot {n : ℕ} (S : Type) : S ⊕ Fin (n+1) ≃ (S ⊕ Unit) ⊕ Fin n where
  toFun := Sum.elim (fun s => Sum.inl (Sum.inl s))
    (Fin.cases (Sum.inl (Sum.inr ())) Sum.inr)
  invFun := Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr 0)) (fun i => Sum.inr i.succ)
  left_inv := by
    intro s
    rcases s with s|i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  right_inv := by
    rintro ((s|u)|i) <;> rfl

def forestBranches {n : ℕ} (P : Fin (n+1) → Type) :
    (Σi,P i) ≃ P 0 ⊕ (Σi : Fin n,P i.succ) where
  toFun p := Fin.cases (fun z => Sum.inl z) (fun i z => Sum.inr ⟨i,z⟩) p.1 p.2
  invFun := Sum.elim (fun z => ⟨0,z⟩) (fun z => ⟨z.1.succ,z.2⟩)
  left_inv := by
    rintro ⟨i,z⟩
    revert z
    refine Fin.cases ?_ (fun i => ?_) i <;> intro z <;> rfl
  right_inv := by rintro (z|⟨i,z⟩) <;> rfl

def forestShuffle (S T : Type) : (S ⊕ Unit) ⊕ T ≃ (S ⊕ T) ⊕ Unit :=
  ((Equiv.sumAssoc S Unit T).trans
    ((Equiv.refl S).sumCongr (Equiv.sumComm Unit T))).trans (Equiv.sumAssoc S T Unit).symm

def forestOutput {n : ℕ} (S : Type) (P : Fin (n+1) → Type) :
    (S ⊕ (Σi : Fin n,P i.succ)) ⊕ P 0 ≃ S ⊕ (Σi,P i) :=
  ((Equiv.sumAssoc S (Σi : Fin n,P i.succ) (P 0)).trans
    ((Equiv.refl S).sumCongr (Equiv.sumComm _ _))).trans
      ((Equiv.refl S).sumCongr (forestBranches P).symm)

def forestColours (d n : ℕ) : (Fin (n+1) → Fin d) ≃ Fin d × (Fin n → Fin d) where
  toFun a := (a 0,fun i => a i.succ)
  invFun a := Fin.cons a.1 a.2
  left_inv a := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv a := rfl

lemma forestTensor_succ {d n : ℕ} {S : Type} (P : Fin (n+1) → Type) [∀i,Fintype (P i)]
    (A : (S ⊕ Fin (n+1) → Fin d) → ℝ) (B : ∀i,(P i ⊕ Unit → Fin d) → ℝ)
    (c : S ⊕ (Σi,P i) → Fin d) :
    forestTensor P A B c = singleContract
      (fun z => forestTensor (fun i : Fin n => P i.succ)
        (fun a => A (a ∘ forestRoot S)) (fun i => B i.succ) (z ∘ forestShuffle S _))
      (B 0) (c ∘ forestOutput S P) := by
  unfold forestTensor singleContract
  rw [←(forestColours d n).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [show ∀a,(forestColours d n).symm a=Fin.cons a.1 a.2 from fun _ => rfl,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hA : Sum.elim (fun s => c (Sum.inl s)) (Fin.cons z a) =
      (Sum.elim
        (fun s => Sum.elim
          (fun s => (c ∘ forestOutput S P) (Sum.inl s)) (fun _ => z)
            (forestShuffle S (Σi : Fin n,P i.succ) (Sum.inl s))) a) ∘ forestRoot S := by
    funext s
    rcases s with s|i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hA]
  have hB (i : Fin n) :
      B i.succ (Sum.elim (fun p => c (Sum.inr ⟨i.succ,p⟩)) (fun _ => a i)) =
      B i.succ (Sum.elim
        (fun p => Sum.elim (fun s => (c ∘ forestOutput S P) (Sum.inl s)) (fun _ => z)
          (forestShuffle S (Σi : Fin n,P i.succ) (Sum.inr ⟨i,p⟩))) (fun _ => a i)) := rfl
  simp only [hB]
  have h0 : B 0 (Sum.elim (fun p => c (Sum.inr ⟨0,p⟩)) (fun _ => z)) =
      B 0 (Sum.elim (fun p => (c ∘ forestOutput S P) (Sum.inr p)) (fun _ => z)) := rfl
  rw [h0]
  simp only [Function.comp_def]
  ring

theorem AllSplitBound.forest {d n : ℕ} {S : Type} [Fintype S] [Nonempty S]
    (P : Fin n → Type) [∀i,Fintype (P i)] [∀i,Nonempty (P i)]
    {A : (S ⊕ Fin n → Fin d) → ℝ} {B : ∀i,(P i ⊕ Unit → Fin d) → ℝ}
    {M : ℝ} {N : Fin n → ℝ} (hA : AllSplitBound A M) (hB : ∀i,AllSplitBound (B i) (N i)) :
    AllSplitBound (forestTensor P A B) (M*∏i,N i) := by
  induction n generalizing S with
  | zero =>
    let e : S ⊕ (Σi : Fin 0,P i) ≃ S ⊕ Fin 0 :=
      (Equiv.refl S).sumCongr (Equiv.equivOfIsEmpty _ _)
    have hh := hA.reindex e.symm
    have he : forestTensor P A B = fun c => A (c ∘ e.symm) := by
      funext c
      simp only [forestTensor,Fin.prod_univ_zero,mul_one,Fintype.sum_unique]
      congr 1
      funext s
      rcases s with s|i
      · rfl
      · exact Fin.elim0 i
    rw [he,Fin.prod_univ_zero,mul_one]
    exact hh
  | succ n ih =>
    have ha := hA.reindex (forestRoot S)
    have ht := ih (fun i : Fin n => P i.succ) ha (fun i => hB i.succ)
    have hs := ht.reindex (forestShuffle S (Σi : Fin n,P i.succ))
    have hc := (hs.singleContract (hB 0)).reindex (forestOutput S P)
    have he : (M*(∏i : Fin n,N i.succ))*N 0=M*∏i,N i := by
      rw [Fin.prod_univ_succ]; ring
    rw [he] at hc
    convert hc using 1
    ext c
    exact forestTensor_succ P A B c
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def multilinearTensor {d : ℕ} {I : Type} (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) (Point d))
    (c : Unit ⊕ I → Fin d) : ℝ :=
  inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
    (A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))))

lemma multilinear_coordinate_expansion {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) (Point d))
    (v : I → Point d) (o : Fin d) :
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ o) (A v) =
      ∑a : I → Fin d,
        inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ o)
          (A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (a i))) *
        ∏i,inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (a i)) (v i) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : v=fun i => ∑j : Fin d,inner ℝ (b j) (v i) • b j := by
    funext i
    exact (b.sum_repr' (v i)).symm
  conv_lhs => rw [hv]
  rw [A.map_sum]
  simp only [inner_sum,A.map_smul_univ,inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

lemma multilinearTensor_compAlong {d n : ℕ} (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) (Point d))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    (a : Unit ⊕ Fin n → Fin d) :
    multilinearTensor (c.compAlongOrderedFinpartition A B) a =
      forestTensor (fun i => Fin (c.partSize i)) (multilinearTensor A)
        (fun i q => multilinearTensor (B i) (q ∘ Equiv.sumComm Unit (Fin (c.partSize i))))
        (a ∘ (Equiv.refl Unit).sumCongr c.equivSigma) := by
  unfold multilinearTensor forestTensor
  rw [OrderedFinpartition.compAlongOrderFinpartition_apply,multilinear_coordinate_expansion]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem AllSplitBound.compAlong {d n : ℕ} (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) (Point d))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    {M : ℝ} {N : Fin c.length → ℝ}
    (hA : AllSplitBound (multilinearTensor A) M)
    (hB : ∀i,AllSplitBound (multilinearTensor (B i)) (N i)) :
    AllSplitBound (multilinearTensor (c.compAlongOrderedFinpartition A B)) (M*∏i,N i) := by
  let (i : Fin c.length) : Nonempty (Fin (c.partSize i)) := Fin.pos_iff_nonempty.mp (c.partSize_pos i)
  have hf := hA.forest (fun i => Fin (c.partSize i))
    (fun i => (hB i).reindex (Equiv.sumComm Unit (Fin (c.partSize i))))
  have hh := hf.reindex ((Equiv.refl Unit).sumCongr c.equivSigma)
  convert hh using 1
  ext a
  exact multilinearTensor_compAlong c A B a

theorem iteratedFDeriv_comp_allSplit {d n : ℕ} {f g : Point d → Point d} (x : Point d)
    (hf : ContDiffAt ℝ (n:WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (n:WithTop ℕ∞) g (f x))
    (M N : ℕ → ℝ) (hM : ∀k,0≤M k) (hN : ∀k,0≤N k)
    (hG : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k g (f x))) (M k))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (N k)) :
    AllSplitBound (multilinearTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      (∑c : OrderedFinpartition n,M c.length * ∏i,N (c.partSize i)) := by
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast le_rfl)]
  have hh := AllSplitBound.finite_sum
    (fun c : OrderedFinpartition n => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))
    (fun c : OrderedFinpartition n => (hG c.length c.length_le).compAlong c _ _
      (fun i => hF (c.partSize i) (c.partSize_le i)))
  convert hh using 1
  funext a
  simp only [FormalMultilinearSeries.taylorComp,multilinearTensor,
    sum_apply,inner_sum,FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]
end LogConcaveSampling.TensorEnergy

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators RealInnerProductSpace NNReal

namespace JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma jet_eq_iteratedFDeriv {ι : Type*} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : ι → E) (l : List ι) (x : E) :
    jet v l f x=iteratedFDeriv ℝ l.length f x (fun i => v (l.get i)) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have he : jet v l f=fun z => iteratedFDeriv ℝ l.length f z (fun i => v (l.get i)) := funext ih
    simp only [jet,he,List.length_cons]
    rw [(hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top l.length : (l.length:WithTop ℕ∞)<(⊤:ℕ∞)) x).iteratedFDeriv_succ_apply_left']
    rfl

lemma jet_finRange_eq_iteratedFDeriv {n : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (v : Fin n → E) (x : E) :
    jet v (List.finRange n) f x=iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ]
    simp only [jet,jet_map]
    have he : jet (v ∘ Fin.succ) (List.finRange n) f=fun z => iteratedFDeriv ℝ n f z (Fin.tail v) :=
      funext (fun z => ih _ z)
    rw [he,(hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n) x).iteratedFDeriv_succ_apply_left']
    rfl
end JetCalculus

lemma multilinearTensor_iterated_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (n : ℕ) (y : Point d) (c : Unit ⊕ Fin n → Fin d) :
    TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y) c=
      ρ^n*((lam:ℝ)*r)*normalizedTensor F x r ρ ((lam:ℝ)*r) y
        (Sum.elim (fun _ => false) (fun _ => true))
        ((List.finRange n).map Sum.inl++[Sum.inr ()]) (c ∘ Equiv.sumComm (Fin n) Unit) := by
  let L := innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
  have hm := conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1
  have hh := conditionalFieldMean_jet_normalized hF x hr hlam hl hρ0 hρ1 y
    (List.finRange n) (by simp) (c ∘ Equiv.sumComm (Fin n) Unit)
  change JetCalculus.jet (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
    (List.finRange n) (L ∘ conditionalFieldMean F x r ρ) y=_ at hh
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hm)] at hh
  rw [L.iteratedFDeriv_comp_left hm.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))] at hh
  simpa only [Fintype.card_fin,ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, L,
    innerSL_apply_apply,TensorEnergy.multilinearTensor] using hh

lemma conditionalMean_iterated_allSplit {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2)) := by
  have hb := normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ : Fin n => false) (fun _ : Unit => true))
    ((List.finRange n).map Sum.inl++[Sum.inr ()])
    (by
      simpa using JetCalculus.nodup_sum_append (List.nodup_finRange n)
        (by simp : ([()] : List Unit).Nodup)) (by intro t; cases t <;> simp)
  have hrb := (hb.reindex (Equiv.sumComm (Fin n) Unit)).const_mul (ρ^n*((lam:ℝ)*r))
  simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique] at hrb
  have hh := hrb.mono (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _)) (show
      ρ^n*((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2)≤
      ((lam:ℝ)*r)*normalizedTensorMajorant (n+1) (1-ρ^2) by
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _))
      (pow_le_one₀ hρ0 hρ1.le))
  convert hh using 1
  funext c
  exact multilinearTensor_iterated_mean hF x hr hlam hl hρ0 hρ1 n y c
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def arrayTensor {d : ℕ} {S I : Type}
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) ((S → Fin d) → ℝ))
    (c : S ⊕ I → Fin d) : ℝ :=
  A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i)))
    (fun s => c (Sum.inl s))

lemma arrayTensor_coordinate_expansion {d : ℕ} {S I : Type} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]
    (A : ContinuousMultilinearMap ℝ (fun _ : I => Point d) ((S → Fin d) → ℝ))
    (v : I → Point d) (o : S → Fin d) :
    A v o=∑a : I → Fin d,A (fun i => EuclideanSpace.basisFun (Fin d) ℝ (a i)) o*
      ∏i,inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (a i)) (v i) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : v=fun i => ∑j : Fin d,inner ℝ (b j) (v i) • b j := by
    funext i
    exact (b.sum_repr' (v i)).symm
  conv_lhs => rw [hv]
  rw [A.map_sum]
  simp only [A.map_smul_univ,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma arrayTensor_compAlong {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) ((S → Fin d) → ℝ))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    (a : S ⊕ Fin n → Fin d) :
    arrayTensor (c.compAlongOrderedFinpartition A B) a=
      forestTensor (fun i => Fin (c.partSize i)) (arrayTensor A)
        (fun i q => multilinearTensor (B i) (q ∘ Equiv.sumComm Unit (Fin (c.partSize i))))
        (a ∘ (Equiv.refl S).sumCongr c.equivSigma) := by
  unfold arrayTensor forestTensor
  rw [OrderedFinpartition.compAlongOrderFinpartition_apply,arrayTensor_coordinate_expansion]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

lemma AllSplitBound.array_compAlong {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (c : OrderedFinpartition n)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin c.length => Point d) ((S → Fin d) → ℝ))
    (B : ∀i,ContinuousMultilinearMap ℝ (fun _ : Fin (c.partSize i) => Point d) (Point d))
    {M : ℝ} {N : Fin c.length → ℝ}
    (hA : AllSplitBound (arrayTensor A) M)
    (hB : ∀i,AllSplitBound (multilinearTensor (B i)) (N i)) :
    AllSplitBound (arrayTensor (c.compAlongOrderedFinpartition A B)) (M*∏i,N i) := by
  let (i : Fin c.length) : Nonempty (Fin (c.partSize i)) := Fin.pos_iff_nonempty.mp (c.partSize_pos i)
  have hf := hA.forest (fun i => Fin (c.partSize i))
    (fun i => (hB i).reindex (Equiv.sumComm Unit (Fin (c.partSize i))))
  have hh := hf.reindex ((Equiv.refl S).sumCongr c.equivSigma)
  convert hh using 1
  ext a
  exact arrayTensor_compAlong c A B a

lemma iteratedFDeriv_array_comp_allSplit {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    {f : Point d → Point d} {g : Point d → (S → Fin d) → ℝ} (x : Point d)
    (hf : ContDiffAt ℝ (n:WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (n:WithTop ℕ∞) g (f x))
    (M N : ℕ → ℝ) (hM : ∀k,0≤M k) (hN : ∀k,0≤N k)
    (hG : ∀k≤n,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g (f x))) (M k))
    (hF : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f x)) (N k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (g ∘ f) x))
      (∑c : OrderedFinpartition n,M c.length*∏i,N (c.partSize i)) := by
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast le_rfl)]
  have hh := AllSplitBound.finite_sum
    (fun c : OrderedFinpartition n => mul_nonneg (hM _) (Finset.prod_nonneg (fun i _ => hN _)))
    (fun c : OrderedFinpartition n => (hG c.length c.length_le).array_compAlong c _ _
      (fun i => hF (c.partSize i) (c.partSize_le i)))
  convert hh using 1
  funext a
  simp only [FormalMultilinearSeries.taylorComp,arrayTensor,
    sum_apply,Finset.sum_apply,FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]

lemma spatialTensor_eq_arrayTensor {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) :
    spatialTensor (fun c z => g z c) (List.finRange n) y=
      fun c => arrayTensor (iteratedFDeriv ℝ n g y) (c ∘ Equiv.sumComm S (Fin n)) := by
  funext c
  let L : ((S → Fin d) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (fun s => c (Sum.inr s))
  dsimp [spatialTensor]
  change JetCalculus.jet _ _ (L ∘ g) y=_
  rw [JetCalculus.jet_finRange_eq_iteratedFDeriv (L.contDiff.comp hg),
    L.iteratedFDeriv_comp_left hg.contDiffAt (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  rfl
lemma AllSplitBound.of_spatialTensor {d n : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g) (y : Point d) {C : ℝ}
    (h : AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange n) y) C) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n g y)) C := by
  rw [spatialTensor_eq_arrayTensor hg y] at h
  have hh := h.reindex (Equiv.sumComm (Fin n) S)
  simpa only [Function.comp_def,Equiv.sumComm_apply,Sum.swap_swap] using hh

end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
