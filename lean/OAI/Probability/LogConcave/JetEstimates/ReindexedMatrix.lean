import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ProperSplitCard
import OAI.Probability.LogConcave.Sampling.ScoreSlots

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace TensorEnergy
lemma Bound.sum_norm {I O J : Type*} [Fintype I] [Fintype O]
    (s : Finset J) {A : J → Matrix O I ℝ} {M : J → ℝ}
    (hM : ∀j∈s,0≤M j) (h : ∀j∈s,Bound (A j) ((M j)^2)) :
    Bound (fun o i => ∑j∈s,A j o i) ((∑j∈s,M j)^2) := by
  have he : (fun o i => ∑j∈s,A j o i)=∑j∈s,A j := by
    ext o i
    exact (Matrix.sum_apply o i s A).symm
  rw [he]
  apply (bound_iff_norm_le (Finset.sum_nonneg hM)).mpr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => (h j hj).norm_le (hM j hj)))

lemma AllSplitBound.sum {S J : Type} [Fintype S] {d : ℕ}
    (s : Finset J) {T : J → (S → Fin d) → ℝ} {M : J → ℝ}
    (hM : ∀j∈s,0≤M j) (h : ∀j∈s,AllSplitBound (T j) (M j)) :
    AllSplitBound (fun a => ∑j∈s,T j a) (∑j∈s,M j) := by
  intro I O _ _ _ _ _ _ e
  exact Bound.sum_norm s hM (fun j hj => h j hj I O e)

lemma splitEnvelope_le_pow {S : Type} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (hM : 0≤M) (h : AllSplitBound T M) :
    splitEnvelope T ≤ (2:ℝ)^Fintype.card S*M :=
  (splitEnvelope_le hM h).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast properSplit_card_le (S:=S)) hM)
end TensorEnergy

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma natural_moment_sum_finset {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀i∈s,AEStronglyMeasurable (f i) μ) (hf0 : ∀i∈s,∀x,0≤f i x)
    {n : ℕ} (hn : 0<n) (B : ι → ℝ≥0∞)
    (hB : ∀i∈s,(∫⁻x,ENNReal.ofReal (f i x)^n ∂μ)≤B i^n) :
    (∫⁻x,ENNReal.ofReal (∑i∈s,f i x)^n ∂μ)≤(∑i∈s,B i)^n := by
  apply (norm_le_iff_natural_moment (μ:=μ)
    (fun x => Finset.sum_nonneg (fun i hi => hf0 i hi x)) hn _).mp
  have hnorm {summand : Ω → ℝ} (hsm : AEStronglyMeasurable summand μ) :
      eLpNorm summand (n:ℝ≥0∞) μ = eLpNorm' summand (n:ℝ) μ := by
    simpa only [ENNReal.coe_natCast,NNReal.coe_natCast] using
      (eLpNorm_nnreal_eq_eLpNorm' (p:=(n:NNReal)) (by exact_mod_cast hn.ne') hsm)
  rw [←hnorm (s.aestronglyMeasurable_fun_sum hf)]
  have hh := eLpNorm_sum_le (μ:=μ) (s:=s) (f:=f)
    (show 1≤(n:ℝ≥0∞) by exact_mod_cast hn)
  have he : (fun x => ∑i∈s,f i x)=∑i∈s,f i := by ext x; simp
  rw [he]
  apply hh.trans
  apply Finset.sum_le_sum
  intro index hindex
  rw [hnorm (hf index hindex)]
  exact (norm_le_iff_natural_moment (μ:=μ) (hf0 index hindex) hn _).mpr (hB index hindex)

lemma natural_moment_mul {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀x,0≤f x) (_hg0 : ∀x,0≤g x) (n : ℕ) (A B : ℝ≥0∞)
    (hA : (∫⁻x,ENNReal.ofReal (f x)^(2*n) ∂μ)≤A^(2*n))
    (hB : (∫⁻x,ENNReal.ofReal (g x)^(2*n) ∂μ)≤B^(2*n)) :
    (∫⁻x,ENNReal.ofReal (f x*g x)^n ∂μ)≤(A*B)^n := by
  let F : Bool → Ω → ℝ≥0∞ := fun b x => if b then ENNReal.ofReal (f x)^n else ENNReal.ofReal (g x)^n
  let M : Bool → ℝ≥0∞ := fun b => if b then A^n else B^n
  have hmm : ∀b∈(Finset.univ : Finset Bool),(∫⁻x,(F b x)^(Finset.univ : Finset Bool).card ∂μ)≤(M b)^(Finset.univ : Finset Bool).card := by
    intro b _
    cases b <;> simpa only [F,M,Bool.false_eq_true,↓reduceIte,Finset.card_univ,Fintype.card_bool,
      ←pow_mul,Nat.mul_comm n 2] using (show _ from (by first | exact hB | exact hA))
  have hff : ∀b∈(Finset.univ : Finset Bool),AEMeasurable (F b) μ := by
    intro b _
    cases b
    · exact (ENNReal.measurable_ofReal.comp_aemeasurable hg.aemeasurable).pow_const n
    · exact (ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable).pow_const n
  have hh := NetworkMoments.lintegral_prod_le Finset.univ Finset.univ_nonempty hff hmm
  simpa only [F,M,Fintype.prod_bool,Bool.false_eq_true,↓reduceIte,
    ENNReal.ofReal_mul (hf0 _),mul_pow] using hh

lemma natural_moment_const_mul {f : Ω → ℝ} (_hf0 : ∀x,0≤f x)
    (n : ℕ) {C : ℝ} (hC : 0≤C) (B : ℝ≥0∞)
    (hB : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ)≤B^n) :
    (∫⁻x,ENNReal.ofReal (C*f x)^n ∂μ)≤(ENNReal.ofReal C*B)^n := by
  simp only [ENNReal.ofReal_mul hC,mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  exact mul_le_mul' le_rfl hB

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace TensorEnergy
def reindexedMatrix {I J K L : Type} (A : Matrix I J ℝ) (e : K ≃ I) (f : L ≃ J) :
    Matrix K L ℝ := fun k l => A (e k) (f l)

lemma matrix_norm_reindex {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix I J ℝ) (e : K ≃ I) (f : L ≃ J) :
    ‖reindexedMatrix A e f‖=‖A‖ := by
  apply le_antisymm
  · exact ((bound_norm A).reindex e f).norm_le (norm_nonneg _)
  · have hh := (bound_norm (reindexedMatrix A e f)).reindex e.symm f.symm
    simpa only [reindexedMatrix,Equiv.apply_symm_apply] using hh.norm_le (norm_nonneg _)

def splitFin {S : Type} [Fintype S] (p : ProperSplit S) :
    S ≃ Fin (Fintype.card (OutSlots p)) ⊕ Fin (Fintype.card (InSlots p)) :=
  (splitEquiv p).trans ((Equiv.sumComm (InSlots p) (OutSlots p)).trans
    ((Fintype.equivFin (OutSlots p)).sumCongr (Fintype.equivFin (InSlots p))))

lemma spatialAdjoint_matrix_norm {K S : Type} [Fintype K] [Fintype S] {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (p : ProperSplit (K ⊕ S)) (y : Point d) :
    ‖splitMatrix (spatialAdjointLeading H F l y) p‖=
      ‖CycleTrace.adjointMatrix H (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun a z => spatialInside F l (a ∘ splitFin p) z) y‖ := by
  let e := Equiv.arrowCongr (Fintype.equivFin (OutSlots p)) (Equiv.refl (Fin d))
  let f := Equiv.arrowCongr (Fintype.equivFin (InSlots p)) (Equiv.refl (Fin d))
  let B := CycleTrace.adjointMatrix H (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun a z => spatialInside F l (a ∘ splitFin p) z) y
  have he : splitMatrix (spatialAdjointLeading H F l y) p=reindexedMatrix B e f := by
    ext o i
    unfold splitMatrix spatialAdjointLeading reindexedMatrix B CycleTrace.adjointMatrix
    congr 2
    funext t
    unfold splitFin
    cases h : splitEquiv p t <;> simp [h,e,f]
  rw [he]
  exact matrix_norm_reindex B e f
end TensorEnergy

theorem spatialAdjoint_split_eLpNorm {S : Type} [Fintype S] {d s : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (N : ℕ → Point d → ℝ) (hN0 : ∀e x,0≤N e x)
    (hN : ∀e x,TensorEnergy.AllSplitBound
      (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*(s+1)) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e)
    (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
    eLpNorm (fun x => ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖)
      (2*(s+1):ℝ≥0∞) (gibbs H)≤
      (3*(2*(s+1))+1)*(d:ℝ≥0∞)^((Fintype.card (TensorEnergy.OutSlots p):ℝ)/(2*(s+1):ℝ))*
        A^(2*(j+1))*R^(k+j+1) := by
  simp_rw [TensorEnergy.spatialAdjoint_matrix_norm]
  apply adjoint_eLpNorm _ _ (Fintype.card_pos) (Fintype.card_pos) hH ht hK
    (fun _ _ => spatialInside_polySmooth F hF _ _ _) (fun e => spatialEnvelope F (j+e)) N
    (fun e x => spatialEnvelope_nonneg F _ x) hN0
    (fun e x => ?_) hN j k A R hA hR hAf hRf
    (fun e => (ENNReal.measurable_ofReal.comp (spatialEnvelope_measurable F hF _)).aemeasurable) hp hh
  simpa only [Fintype.card_fin] using fieldPosition_spatialInside_allSplit F hF
    (List.finRange j) (List.nodup_finRange j) (by simp) (TensorEnergy.splitFin p) e x

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

lemma spatialAdjoint_polySmooth {K S : Type} {d : ℕ} {H : Point d → ℝ}
    (hH : PolySmooth H) (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (l : List K) (c : K ⊕ S → Fin d) :
    PolySmooth (fun y => spatialAdjointLeading H F l y c) :=
  hH.tensorAdjoint (fun z => spatialInside_polySmooth F hF l c z) _

lemma traceDimensionRoot {d j a c n : ℕ} (hd : 1≤d) (hc : 1≤c) (hn : 2≤n)
    (ha : a≤j+c) :
    (d:ℝ≥0∞)^((a:ℝ)/(2*(traceMomentOrder d j c n:ℝ)))≤ENNReal.ofReal (Real.exp (1/2)) := by
  have ht := traceMomentOrder_bounds (d:=d) (j:=j) (by exact_mod_cast hc : (1:ℝ)≤c)
    (by exact_mod_cast hn : (2:ℝ)≤n)
  have hs : 0<(traceMomentOrder d j c n:ℝ) := by exact_mod_cast ht.1
  have hupper := traceMomentOrder_dimension_root (d:=d) (j:=j) hd
    (by exact_mod_cast hc : (1:ℝ)≤c) (by exact_mod_cast hn : (2:ℝ)≤n)
  apply (ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd : (1:ℝ≥0∞)≤d)
    (div_le_div_of_nonneg_right (by exact_mod_cast ha : (a:ℝ)≤j+(c:ℝ)) (by positivity))).trans
  rw [←ENNReal.ofReal_natCast d,
    ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg d) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hupper

theorem spatialAdjoint_envelope_moment {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (N : ℕ → Point d → ℝ) (hN0 : ∀e x,0≤N e x)
    (hN : ∀e x,TensorEnergy.AllSplitBound
      (CycleTrace.scorePosition H (EuclideanSpace.basisFun (Fin d) ℝ) e x) (N e x))
    (j k n : ℕ) (hd : 1≤d) (hn : 2≤n)
    (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hp : ∀e≤2*traceMomentOrder d j (Fintype.card S+1) n,
      (∫⁻x,ENNReal.ofReal (spatialEnvelope F (j+e) x)^(2*traceMomentOrder d j (Fintype.card S+1) n) ∂gibbs H)≤
      (A^(j+e+1)*R^(k+j+e))^(2*traceMomentOrder d j (Fintype.card S+1) n))
    (hh : ∀e≤2*traceMomentOrder d j (Fintype.card S+1) n,∀x,
      ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    (∫⁻x,ENNReal.ofReal (TensorEnergy.splitEnvelope (spatialAdjointLeading H F (List.finRange j) x))^n ∂gibbs H)≤
      ((2:ℝ≥0∞)^(j+Fintype.card S)*
        ((3*(2*traceMomentOrder d j (Fintype.card S+1) n)+1)*ENNReal.ofReal (Real.exp (1/2))*
          A^(2*(j+1))*R^(k+j+1)))^n := by
  let t := traceMomentOrder d j (Fintype.card S+1) n
  have ht0 : 0<t := (traceMomentOrder_bounds (d:=d) (j:=j)
    (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card S); linarith : (1:ℝ)≤(Fintype.card S:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).1
  have hn2 : n≤2*t := by
    change n≤2*traceMomentOrder d j (Fintype.card S+1) n
    exact_mod_cast (traceMomentOrder_bounds (d:=d) (j:=j)
      (by have := Nat.cast_nonneg (α:=ℝ) (Fintype.card S); linarith : (1:ℝ)≤(Fintype.card S:ℝ)+1) (by exact_mod_cast hn : (2:ℝ)≤n)).2.1
  have he : t-1+1=t := Nat.sub_add_cancel ht0
  have heR : ((t-1:ℕ):ℝ≥0∞)+1=(t:ℝ≥0∞) := by exact_mod_cast he
  have heQ : (t-1:ℕ)+1=t := he
  have heQ' : ((t-1:ℕ):ℝ)+1=(t:ℝ) := by exact_mod_cast heQ
  have hmeas (c : Fin j ⊕ S → Fin d) : Measurable (fun x => spatialAdjointLeading H F (List.finRange j) x c) :=
    (spatialAdjoint_polySmooth hH F hF _ c).smooth.continuous.measurable
  have hlarge (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
      eLpNorm (fun x => ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖)
        (2*t:ℝ≥0∞) (gibbs H)≤
      (3*(2*t)+1)*ENNReal.ofReal (Real.exp (1/2))*A^(2*(j+1))*R^(k+j+1) := by
    have h := spatialAdjoint_split_eLpNorm (s:=t-1) hH ht hK F hF N hN0 hN j k A R hA hR hAf hRf
      (by simpa only [he] using hp) (by simpa only [he] using hh) p
    simp only [heR,heQ'] at h
    have hcard : Fintype.card (TensorEnergy.OutSlots p)≤j+(Fintype.card S+1) := by
      have hh := Fintype.card_subtype_le (fun s : Fin j ⊕ S => ¬p.val s=true)
      change Fintype.card (TensorEnergy.OutSlots p)≤_ at hh
      simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_assoc,Nat.succ_eq_add_one] using hh.trans (Nat.le_succ _)
    have hroot := traceDimensionRoot (d:=d) (j:=j) (a:=Fintype.card (TensorEnergy.OutSlots p))
      (c:=Fintype.card S+1) (n:=n) hd (Nat.le_add_left 1 _) hn hcard
    simp only [Nat.cast_add,Nat.cast_one] at hroot
    exact h.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hroot) le_rfl) le_rfl)
  have hsmall (p : TensorEnergy.ProperSplit (Fin j ⊕ S)) :
      (∫⁻x,ENNReal.ofReal ‖TensorEnergy.splitMatrix (spatialAdjointLeading H F (List.finRange j) x) p‖^n ∂gibbs H)≤
      ((3*(2*t)+1)*ENNReal.ofReal (Real.exp (1/2))*A^(2*(j+1))*R^(k+j+1))^n := by
    apply (norm_le_iff_natural_moment (μ:=gibbs H) (fun _ => norm_nonneg _) (by omega) _).mp
    have hnorm := eLpNorm_nnreal_eq_eLpNorm' (μ:=gibbs H) (p:=(n:ℝ≥0))
      (by exact_mod_cast (show n ≠ 0 by omega))
      (TensorEnergy.measurable_splitMatrix_norm _ hmeas p).aestronglyMeasurable
    simp only [ENNReal.coe_natCast,NNReal.coe_natCast] at hnorm
    rw [←hnorm]
    apply (eLpNorm_le_eLpNorm_of_exponent_le
      (show (n:ℝ≥0∞)≤2*(t:ℝ≥0∞) by exact_mod_cast hn2)).trans
    exact hlarge p
  simpa only [Fintype.card_sum,Fintype.card_fin] using
    TensorEnergy.moment_splitEnvelope (gibbs H) (spatialAdjointLeading H F (List.finRange j))
      hmeas (by omega : 0<n) _ hsmall

end LogConcaveSampling

end

end

end

end OAI
