import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteDynkinDifference
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts

namespace OAI

/-! # Polynomial speed of a conjugated nilpotent one-parameter subgroup -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold Topology

variable {E G J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [Fintype J]

/-- In a nilpotent group, conjugating a fixed exponential line by a ray
costs a polynomial in the ray parameter, retaining its linear time factor. -/
theorem exists_nilpotent_conjugation_coordinate_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥)
    (b : Basis J ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (s : ℝ), |s| ≤ 1 →
      ‖b.equivFun (chart.symm
        (Exp (-(n : ℝ) • v) * Exp (s • u) * Exp ((n : ℝ) • v)))‖ ≤
          A * (1 + n) ^ c * |s| := by
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 3
  obtain ⟨C, hC, hbr⟩ := exists_basis_structureConstant_bound b
  obtain ⟨B, hB, hdiff⟩ := exists_finiteDynkinPolynomial_difference_bound b coeff hC hbr
  let U := ‖b.equivFun u‖
  let V := ‖b.equivFun v‖
  have hU : 0 ≤ U := norm_nonneg _
  have hV : 0 ≤ V := norm_nonneg _
  refine ⟨B * (1 + U + V) ^ c * U, by positivity, ?_⟩
  intro n s hs
  let X : Fin 3 → GroupLieAlgebra (𝓘(ℝ, E)) G := ![-(n : ℝ) • v, s • u, (n : ℝ) • v]
  let Y : Fin 3 → GroupLieAlgebra (𝓘(ℝ, E)) G := ![-(n : ℝ) • v, 0, (n : ℝ) • v]
  let M := (n : ℝ) * V + U
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hX (i : Fin 3) : ‖b.equivFun (X i)‖ ≤ M := by
    fin_cases i <;> simp [X, map_smul, norm_smul, Real.norm_eq_abs]
    · change (n : ℝ) * V ≤ M
      dsimp [M]; linarith
    · change |s| * U ≤ M
      dsimp [M]; nlinarith
    · change (n : ℝ) * V ≤ M
      dsimp [M]; linarith
  have hY (i : Fin 3) : ‖b.equivFun (Y i)‖ ≤ M := by
    fin_cases i
    · simpa [X, Y] using hX 0
    · simpa [Y] using hM
    · simpa [X, Y] using hX 2
  have hXY (i : Fin 3) : ‖b.equivFun (X i - Y i)‖ ≤ U * |s| := by
    fin_cases i
    · simpa [X, Y] using mul_nonneg hU (abs_nonneg s)
    · simp [X, Y, U, norm_smul, Real.norm_eq_abs, mul_comm]
    · simpa [X, Y] using mul_nonneg hU (abs_nonneg s)
  have hYzero : finiteDynkinPolynomial coeff Y = 0 := by
    apply chart.injective
    rw [hchart, hchart, hExp.map_zero]
    have hy := (hprod Y).symm
    simpa [Y, List.ofFn_succ, neg_smul, hExp.map_neg, hExp.map_zero] using hy
  have hproduct : Exp (-(n : ℝ) • v) * Exp (s • u) * Exp ((n : ℝ) • v) =
      Exp (finiteDynkinPolynomial coeff X) := by
    simpa [X, List.ofFn_succ, mul_assoc] using hprod X
  have hh := hdiff X Y M (U * |s|) hM (mul_nonneg hU (abs_nonneg s)) hX hY hXY
  rw [hYzero, sub_zero] at hh
  have hp : (1 + M) ^ c ≤ ((1 + U + V) * (1 + (n : ℝ))) ^ c := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [M]
    nlinarith
  rw [hproduct, ← hchart, chart.symm_apply_apply]
  apply hh.trans
  calc
    B * (1 + M) ^ c * (U * |s|) ≤ B * ((1 + U + V) * (1 + (n : ℝ))) ^ c * (U * |s|) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end PolycyclicRecognition

end

end OAI
