import OAI.Analysis.SeparableQuotients.PathOperators

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming

def Family.at : ℕ → Family
  | 0 => .mixed
  | k+1 => .pure k
@[simp] lemma Family.at_index (f : Family) : Family.at f.index = f := by cases f <;> rfl
@[simp] lemma Family.index_at (n : ℕ) : (Family.at n).index = n := by cases n <;> rfl
lemma Family.at_injective : Function.Injective Family.at := fun _ _ h => by
  simpa using congrArg Family.index h
end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace

private lemma cachedNormedT2 (Y : Type*) [NormedAddCommGroup Y] : T2Space Y := inferInstance
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance opDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance opDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance opXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance opWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance opWSpace : NormedSpace ℝ W := inferInstance
local instance opWT2 : T2Space W := @cachedNormedT2 W opWGroup

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

def labelAnalysis (f : Family) : StrongDual ℝ E →L[ℝ] lp (fun _ : PathIndex f => ℝ) f.pathExponent :=
  LpCoding.analysisMap f.pathConjugate (labelMap hCH f)

@[simp] lemma labelAnalysis_apply (f : Family) (y : StrongDual ℝ E) (P : PathIndex f) :
    labelAnalysis hCH f y P = y (e (pathLabel hCH f P)) := by
  change y (labelMap hCH f (lp.single f.sourceExponent P 1)) = _
  rw [labelMap_single,one_smul]

lemma norm_labelAnalysis_le (f : Family) : ‖labelAnalysis hCH f‖ ≤ 1 :=
  (LpCoding.norm_analysisMap_le _ _).trans (norm_labelMap_le hCH f)

def familyOperator (f : Family) : StrongDual ℝ E →L[ℝ] W :=
  (pathMap f).comp (labelAnalysis hCH f)

lemma norm_familyOperator_le (f : Family) : ‖familyOperator hCH f‖ ≤ 1 := by
  calc
    _ ≤ ‖pathMap f‖ * ‖labelAnalysis hCH f‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul (norm_pathMap_le f) (norm_labelAnalysis_le hCH f)
      (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma labelAnalysis_coordinate_self (f : Family) (P : PathIndex f) :
    labelAnalysis hCH f (coordinate (pathLabel hCH f P)) = lp.single f.pathExponent P 1 := by
  apply lp.ext
  funext Q
  simp only [labelAnalysis_apply,coordinate_e,lp.single_apply,Pi.single_apply]
  have he : pathLabel hCH f P = pathLabel hCH f Q ↔ P=Q := (pathLabelEmb hCH f).injective.eq_iff
  simp only [he,eq_comm]

lemma labelAnalysis_coordinate_other (f g : Family) (P : PathIndex f) (hfg : f ≠ g) :
    labelAnalysis hCH g (coordinate (pathLabel hCH f P)) = 0 := by
  apply lp.ext
  funext Q
  have hn : pathLabel hCH f P ≠ pathLabel hCH g Q := by
    intro h
    have hs : (Sigma.mk f P : (t : Family) × PathIndex t) = Sigma.mk g Q :=
      pathLabel_injective hCH h
    exact hfg (congrArg Sigma.fst hs)
  simp [labelAnalysis_apply,coordinate_e,hn]

lemma familyOperator_coordinate (f g : Family) (P : PathIndex f) :
    familyOperator hCH g (coordinate (pathLabel hCH f P)) =
      if f=g then pathCoset P else 0 := by
  by_cases h : f=g
  · subst g
    simp [familyOperator,labelAnalysis_coordinate_self]
  · simp [familyOperator,labelAnalysis_coordinate_other hCH f g P h,h]

def tau (n : ℕ) : ℝ := (1/32)*(1/2)^n
lemma tau_pos (n : ℕ) : 0 < tau n := by unfold tau; positivity
lemma tau_hasSum : HasSum tau (1/16) := by
  have h := (hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)).mul_left (1/32:ℝ)
  norm_num at h
  exact h
lemma tau_summable : Summable tau := tau_hasSum.summable

lemma operator_summable : Summable (fun n => tau n • familyOperator hCH (Family.at n)) := by
  apply tau_summable.of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
  exact mul_le_of_le_one_right (tau_pos n).le (norm_familyOperator_le hCH _)

/-- The CH perturbation operator with norm at most 1/10. -/
def B : StrongDual ℝ E →L[ℝ] W := ∑' n, tau n • familyOperator hCH (Family.at n)

lemma norm_B_le : ‖B hCH‖ ≤ 1/10 := by
  have hb : ‖B hCH‖ ≤ 1/16 := by
    apply tsum_of_norm_bounded tau_hasSum
    intro n
    rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
    exact mul_le_of_le_one_right (tau_pos n).le (norm_familyOperator_le hCH _)
  linarith

lemma B_coordinate (f : Family) (P : PathIndex f) :
    B hCH (coordinate (pathLabel hCH f P)) = tau f.index • pathCoset P := by
  have hsum := (ContinuousLinearMap.apply ℝ W (coordinate (pathLabel hCH f P))).hasSum
    (operator_summable hCH).hasSum
  have hf : (fun n => (tau n • familyOperator hCH (Family.at n))
      (coordinate (pathLabel hCH f P))) =
      (fun n => if n=f.index then tau f.index • pathCoset P else 0) := by
    funext n
    rw [smul_apply,familyOperator_coordinate]
    by_cases h : n=f.index
    · subst n; simp
    · have hn : f ≠ Family.at n := by
        intro hf
        apply h
        rw [hf,Family.index_at]
      simp [h,hn]
  have he := hasSum_ite_eq f.index (tau f.index • pathCoset P)
  exact hsum.unique (by simpa only [ContinuousLinearMap.apply_apply,hf] using he)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance propDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance propDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
local instance propXClosed : IsClosed (X₀ : Set (StrongDual ℝ E)) := norming.predual_isClosed
@[reducible] local instance propWGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance propWSpace : NormedSpace ℝ W := inferInstance
@[reducible] local instance propWDualGroup : NormedAddCommGroup (StrongDual ℝ W) := inferInstance
@[reducible] local instance propWDualSpace : NormedSpace ℝ (StrongDual ℝ W) := inferInstance

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

lemma pathMap_mem_closed (Z : Submodule ℝ W) (hZ : IsClosed (Z : Set W))
    (f : Family) (hf : ∀ P : PathIndex f, pathCoset P ∈ Z)
    (a : lp (fun _ : PathIndex f => ℝ) f.pathExponent) : pathMap f a ∈ Z := by
  refine (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top).induction_on
    (p := fun a => pathMap f a ∈ Z) a (hZ.preimage (pathMap f).continuous) ?_
  intro c
  rw [pathMap_finite]
  exact Z.sum_mem (fun i _ => Z.smul_mem _ (hf i))

lemma pathCoset_mem_B_predual (f : Family) (P : PathIndex f) :
    pathCoset P ∈ X₀.map (B hCH).toLinearMap := by
  have h : tau f.index • pathCoset P ∈ X₀.map (B hCH).toLinearMap := by
    refine ⟨coordinate (pathLabel hCH f P),norming.coordinate_mem_predual _,?_⟩
    exact B_coordinate hCH f P
  have hh := (X₀.map (B hCH).toLinearMap).smul_mem (tau f.index)⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ (tau_pos _).ne',one_smul] using hh

lemma B_range_mem_predual_closure :
    (B hCH).range ≤ (X₀.map (B hCH).toLinearMap).topologicalClosure := by
  rintro _ ⟨y,rfl⟩
  let Z := (X₀.map (B hCH).toLinearMap).topologicalClosure
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    ((ContinuousLinearMap.apply ℝ W y).hasSum (operator_summable hCH).hasSum)
  apply Eventually.of_forall
  intro s
  simp only [ContinuousLinearMap.apply_apply,smul_apply]
  apply Z.sum_mem
  intro n _
  apply Z.smul_mem
  exact pathMap_mem_closed Z (Submodule.isClosed_topologicalClosure _) (Family.at n)
    (fun P => Submodule.le_topologicalClosure _ (pathCoset_mem_B_predual hCH _ P))
    (labelAnalysis hCH _ y)

def familyVector (f : Family) (w : StrongDual ℝ W) : E :=
  labelMap hCH f (LpCoding.coefficients f.pathConjugate.symm (w.comp (pathMap f)))

lemma norm_familyVector_le (f : Family) (w : StrongDual ℝ W) :
    ‖familyVector hCH f w‖ ≤ ‖w‖ := by
  calc
    _ ≤ ‖labelMap hCH f‖ * ‖LpCoding.coefficients f.pathConjugate.symm (w.comp (pathMap f))‖ :=
      (labelMap hCH f).le_opNorm _
    _ ≤ 1 * ‖w.comp (pathMap f)‖ := mul_le_mul (norm_labelMap_le hCH f)
      (LpCoding.norm_coefficients_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ ‖w‖ := by
      rw [one_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (norm_pathMap_le f))

lemma familyVector_pair (f : Family) (w : StrongDual ℝ W) (y : StrongDual ℝ E) :
    y (familyVector hCH f w) = w (familyOperator hCH f y) := by
  exact LpCoding.eval_coefficients_symm f.pathConjugate f.sourceExponent_ne_top f.pathExponent_ne_top
    (y.comp (labelMap hCH f)) (w.comp (pathMap f))

lemma vector_summable (w : StrongDual ℝ W) :
    Summable (fun n => tau n • familyVector hCH (Family.at n) w) := by
  apply (tau_summable.mul_right ‖w‖).of_norm_bounded
  intro n
  rw [norm_smul,Real.norm_of_nonneg (tau_pos n).le]
  exact mul_le_mul_of_nonneg_left (norm_familyVector_le hCH _ _) (tau_pos n).le

/-- The adjoint perturbation has range in the canonical evaluation image. -/
lemma B_adjoint (w : StrongDual ℝ W) :
    ∃ v : E, w.comp (B hCH) = NormedSpace.inclusionInDoubleDual ℝ E v := by
  refine ⟨∑' n, tau n • familyVector hCH (Family.at n) w,?_⟩
  ext y
  have hB := w.hasSum ((ContinuousLinearMap.apply ℝ W y).hasSum (operator_summable hCH).hasSum)
  have hv := y.hasSum (vector_summable hCH w).hasSum
  have he : (fun n => w ((tau n • familyOperator hCH (Family.at n)) y)) =
      fun n => y (tau n • familyVector hCH (Family.at n) w) := by
    funext n
    simp only [smul_apply,map_smul,familyVector_pair]
  change w (B hCH y) = y (∑' n, tau n • familyVector hCH (Family.at n) w)
  exact hB.unique (by simpa only [ContinuousLinearMap.apply_apply,he] using hv)

end SeparableQuotient.ActualSpace

end

end OAI
