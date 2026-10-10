import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingLogTime
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingFourWindows

namespace OAI

/-!
# Four fixed candidate windows for two moving annuli

The inverse scale at a selected time is in one of two exponential
regimes. Adding the logarithm of a fixed enlargement to both candidate
exponents supplies the second annulus, while keeping all four exponents
in the recurrence range once the logarithmic time window is large.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearing_four_candidate_windows
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    (hsmall : rootShearingKappa i j g ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hlog : Real.log C ≤ rootShearingLogTime i j g) :
    ∃ θ η : Fin 2 × Fin 2 → ℝ,
      (∀ q, 4 * rootShearingLogTime i j g ≤ θ q) ∧
      (∀ q, θ q ≤ 6 * rootShearingLogTime i j g) ∧
      (∀ q, η q = 0 ∨ η q = 1) ∧
      ∀ τ ∈ Icc 0 (rootShearingLogTime i j g), ∃ mode : Fin 2, ∀ b : Fin 2,
        (if b = 0 then 1 else C) *
          (rootShearingKappa i j (rootPairConjugate i j τ g))⁻¹ =
            Real.exp (θ (mode, b) - η (mode, b) * τ) := by
  obtain ⟨v, hvlo, hvhi, hreg⟩ := rootShearingKappa_two_regimes hij g hnot hsmall
  let T := rootShearingLogTime i j g
  have hT : 0 ≤ T := rootShearingLogTime_nonneg hij g hnot hsmall
  have hl : 0 ≤ Real.log C := Real.log_nonneg hC
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let θ : Fin 2 × Fin 2 → ℝ := fun q =>
    (if q.1 = 0 then 4 * T else v) + (if q.2 = 0 then 0 else Real.log C)
  let η : Fin 2 × Fin 2 → ℝ := fun q => if q.1 = 0 then 0 else 1
  refine ⟨θ, η, ?_, ?_, ?_, ?_⟩
  · intro q
    dsimp only [θ]
    split_ifs <;> dsimp only [T] at * <;> linarith
  · intro q
    dsimp only [θ]
    split_ifs <;> dsimp only [T] at * <;> linarith
  · intro q
    dsimp only [η]
    split_ifs <;> tauto
  · intro τ hτ
    rcases hreg τ hτ with h | h
    · refine ⟨0, ?_⟩
      intro b
      rw [h]
      fin_cases b
      · simp [θ, η, T]
      · simp [θ, η, T, Real.exp_add, Real.exp_log hCp, mul_comm]
    · refine ⟨1, ?_⟩
      intro b
      rw [h]
      fin_cases b
      · simp [θ, η]
      · norm_num [θ, η]
        rw [show v + Real.log C - τ = Real.log C + (v - τ) by ring,
          Real.exp_add, Real.exp_log hCp]

end DukePrimeDegree

end

end OAI
