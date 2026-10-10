import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! # The compact polyhedron used for sampling the nilpotent boxes -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

omit [FiniteDimensional ℝ W] in
/-- Each balanced positive-multiplicity basis controls the absolute value
of every generator weight, including its negative part. -/
theorem SupportDatum.abs_weight_le_basisSupport (D : SupportDatum W I B)
    (b : B) (i : I) (x : W) : |D.weight i x| ≤ D.basisSupport b x := by
  classical
  have hpos (y : W) : D.weight i y ≤ D.basisSupport b y := by
    have hn : (1 : ℝ) ≤ D.multiplicity b i := by exact_mod_cast D.positive b i
    calc
      D.weight i y ≤ max 0 (D.weight i y) := le_max_right _ _
      _ ≤ (D.multiplicity b i : ℝ) * max 0 (D.weight i y) :=
        le_mul_of_one_le_left (le_max_left _ _) hn
      _ ≤ D.basisSupport b y := by
        apply Finset.single_le_sum (s := Finset.univ) (f := fun j =>
          (D.multiplicity b j : ℝ) * max 0 (D.weight j y))
        · intro j _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
        · exact Finset.mem_univ i
  have hm := hpos (-x)
  rw [map_neg, D.basisSupport_neg] at hm
  exact abs_le.mpr ⟨by linarith, hpos x⟩

/-- Halfspaces tangent to the unit ball, one per oriented generator ray. -/
def weightSamplingPolytope (α : I → W →L[ℝ] ℝ) : Set W :=
  {x | ∀ i, α i x ≤ ‖α i‖}

/-- Strict halfspaces give its interior sampling region. -/
def weightSamplingInterior (α : I → W →L[ℝ] ℝ) : Set W :=
  {x | ∀ i, α i x < ‖α i‖}

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem isClosed_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    IsClosed (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem convex_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    Convex ℝ (weightSamplingPolytope α) := by
  simp only [weightSamplingPolytope, ofPred_forall]
  exact convex_iInter fun i => convex_halfSpace_le (α i).toLinearMap.isLinear _

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem convex_weightSamplingInterior (α : I → W →L[ℝ] ℝ) :
    Convex ℝ (weightSamplingInterior α) := by
  simp only [weightSamplingInterior, ofPred_forall]
  exact convex_iInter fun i => convex_halfSpace_lt (α i).toLinearMap.isLinear _

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem isOpen_weightSamplingInterior (α : I → W →L[ℝ] ℝ) :
    IsOpen (weightSamplingInterior α) := by
  simp only [weightSamplingInterior, ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (α i).continuous continuous_const

omit [FiniteDimensional ℝ W] [Fintype B] in
theorem weightSamplingInterior_subset_interior (α : I → W →L[ℝ] ℝ) :
    weightSamplingInterior α ⊆ interior (weightSamplingPolytope α) := by
  apply interior_maximal
  · intro x hx i
    exact (hx i).le
  · exact isOpen_weightSamplingInterior α

omit [FiniteDimensional ℝ W] [Fintype B] in
/-- Strict scaled facet inequalities place a point in the scaled interior. -/
theorem mem_smul_weightSamplingInterior (α : I → W →L[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) (x : W) (hx : ∀ i, α i x < a * ‖α i‖) :
    x ∈ (fun y : W => a • y) '' interior (weightSamplingPolytope α) := by
  refine ⟨a⁻¹ • x, weightSamplingInterior_subset_interior α ?_, ?_⟩
  · intro i
    simp only [map_smul, smul_eq_mul]
    exact (inv_mul_lt_iff₀ ha).mpr (hx i)
  · simp [smul_smul, ha.ne']

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem closedBall_subset_weightSamplingPolytope (α : I → W →L[ℝ] ℝ) :
    Metric.closedBall (0 : W) 1 ⊆ weightSamplingPolytope α := by
  intro x hx i
  have hn : ‖x‖ ≤ 1 := by simpa using hx
  exact ((le_abs_self _).trans ((α i).le_opNorm x)).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _))

omit [FiniteDimensional ℝ W] [Fintype B] [Fintype I] in
theorem zero_mem_weightSamplingInterior (α : I → W →L[ℝ] ℝ)
    (hα : ∀ i, α i ≠ 0) : (0 : W) ∈ weightSamplingInterior α := by
  intro i
  simpa using norm_pos_iff.mpr (hα i)

/-- Positive balance and separation make the sampling polyhedron compact.
No boundedness assumption on the polyhedron is needed. -/
theorem SupportDatum.isCompact_weightSamplingPolytope (D : SupportDatum W I B) (b : B) :
    IsCompact (weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap)) := by
  classical
  let α : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi D.weight
  have hα : Function.Injective α := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply D.separates x
    intro i
    exact congrFun hx i
  have hemb := LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hα)
  let C : ℝ := ∑ i, (D.multiplicity b i : ℝ) * ‖(D.weight i).toContinuousLinearMap‖
  have hbound : weightSamplingPolytope (fun i => (D.weight i).toContinuousLinearMap) ⊆
      α ⁻¹' Icc (fun _ => -C) (fun _ => C) := by
    intro x hx
    have hs : D.basisSupport b x ≤ C := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact max_le (norm_nonneg _) (hx i)
    constructor <;> intro i
    · exact neg_le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
    · exact le_of_abs_le ((D.abs_weight_le_basisSupport b i x).trans hs)
  exact (hemb.isCompact_preimage isCompact_Icc).of_isClosed_subset
    (isClosed_weightSamplingPolytope _) hbound

end PolycyclicRecognition

end

end OAI
