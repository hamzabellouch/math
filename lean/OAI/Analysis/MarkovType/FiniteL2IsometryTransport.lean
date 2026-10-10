import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

universe u v w
variable {E : Type u} {G : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [sectionFintypeΩ : Fintype Ω]

omit sectionFintypeΩ in
@[simp] theorem finiteDifference_map [Fintype Ω] (T : E →ₗ[ℝ] G) (M : ℕ → Ω → E)
    (j : ℕ) (ω : Ω) :
    finiteDifference (fun n ω => T (M n ω)) j ω = T (finiteDifference M j ω) := by
  by_cases hj : j = 0
  · subst j
    rfl
  · simp only [finiteDifference, ite_eq_right hj, map_sub]

theorem HasZeroConditionalSum.map {μ : FiniteLaw Ω} {P : Setoid Ω}
    {f : Ω → E} (hf : HasZeroConditionalSum μ P f) (T : E →ₗ[ℝ] G) :
    HasZeroConditionalSum μ P (fun ω => T (f ω)) := by
  classical
  intro a
  calc
    _ = T (∑ ω, if P.r ω a then μ.mass ω • f ω else 0) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : P.r ω a <;> simp only [h, ite_true, ite_false, map_smul, map_zero]
    _ = 0 := by rw [hf a, map_zero]

theorem FinitePartitionFiltration.IsMartingaleUpTo.map
    {F : FinitePartitionFiltration Ω} {μ : FiniteLaw Ω}
    {M : ℕ → Ω → E} {N : ℕ} (hM : F.IsMartingaleUpTo μ M N)
    (T : E →ₗ[ℝ] G) : F.IsMartingaleUpTo μ (fun n ω => T (M n ω)) N := by
  constructor
  · intro j hj ω η hωη
    exact congrArg T (hM.1 j hj hωη)
  · intro j hj hjN
    have h := (hM.2 j hj hjN).map T
    have heq : finiteDifference (fun n ω => T (M n ω)) j =
        fun ω => T (finiteDifference M j ω) := by
      funext ω
      exact finiteDifference_map T M j ω
    rw [heq]
    exact h

@[simp] theorem finiteL2Norm_linearIsometry (T : E →ₗᵢ[ℝ] G)
    (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => T (f ω)) = finiteL2Norm μ f := by
  simp only [finiteL2Norm, T.norm_map]

theorem FiniteUpperL2.pullback_isometry {r χ : ℝ} (h : FiniteUpperL2 G r χ)
    (T : E →ₗᵢ[ℝ] G) : FiniteUpperL2 E r χ := by
  intro m μ F M N B hB hM hdiff
  have hM' := hM.map T.toLinearMap
  have hdiff' : ∀ j : ℕ, j ≤ N →
      finiteL2Norm μ (finiteDifference (fun n ω => T (M n ω)) j) ≤ B := by
    intro j hj
    have heq : finiteDifference (fun n ω => T (M n ω)) j =
        fun ω => T (finiteDifference M j ω) := by
      funext ω
      exact finiteDifference_map T.toLinearMap M j ω
    rw [heq, finiteL2Norm_linearIsometry]
    exact hdiff j hj
  simpa only [finiteL2Norm_linearIsometry] using h m μ F
    (fun n ω => T (M n ω)) N B hB hM' hdiff'

theorem FiniteLowerL2.pullback_isometry {s χ : ℝ} (h : FiniteLowerL2 G s χ)
    (T : E →ₗᵢ[ℝ] G) : FiniteLowerL2 E s χ := by
  intro m μ F M N hM
  have hM' := hM.map T.toLinearMap
  have heq (j : ℕ) : finiteDifference (fun n ω => T (M n ω)) j =
      fun ω => T (finiteDifference M j ω) := by
    funext ω
    exact finiteDifference_map T.toLinearMap M j ω
  simpa only [heq, finiteL2Norm_linearIsometry] using h m μ F
    (fun n ω => T (M n ω)) N hM'

end MarkovSuperreflexivity

end

end OAI
