import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentConjugationCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialCoarseMetric

namespace OAI

/-! # Polynomial coarse speed of right-translated nilpotent lines -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule
open scoped Manifold Topology

variable {E D G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace D] [ChartedSpace E D] [Group D]
  [LieGroup (𝓘(ℝ, E)) ⊤ D] [T2Space D]
  [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- In any continuously embedded nilpotent factor, right translation by
a ray has polynomial coarse speed on each fixed exponential line. -/
theorem exists_nilpotent_right_translate_coarse_metric
    (κ : D →* G) (hκ : Continuous κ)
    (dynkin : NilpotentDynkinExpansionInput E D)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) D → D) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) D ≃ₜ D) (hchart : ∀ x, chart x = Exp x)
    {c : ℕ} (hc : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D)
      (GroupLieAlgebra (𝓘(ℝ, E)) D) c = ⊥)
    {m : ℕ} (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) D))
    (u v : GroupLieAlgebra (𝓘(ℝ, E)) D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (s t : ℝ), |t - s| ≤ 1 →
      dist (κ (Exp (s • u) * Exp ((n : ℝ) • v)))
        (κ (Exp (t • u) * Exp ((n : ℝ) • v))) ≤
          C * (1 + n) ^ c * |t - s| + C := by
  let Φ : (Fin m → ℝ) → G := fun w => κ (Exp (b.equivFun.symm w))
  have hcont : Continuous Φ := by
    have he : Exp = chart := (funext hchart).symm
    exact hκ.comp ((he ▸ chart.continuous).comp b.equivFun.symm.toContinuousLinearEquiv.continuous)
  have hzero : Φ 0 = 1 := by simp [Φ, hExp.map_zero]
  have hmul (w : Fin m → ℝ) (s t : ℝ) : Φ ((s + t) • w) = Φ (s • w) * Φ (t • w) := by
    simp only [Φ, map_smul, hExp.map_add_smul, map_mul]
  obtain ⟨B, hB, hmetric⟩ := continuous_radial_exponential_metric_bound Φ hcont hzero hmul
  obtain ⟨A, hA, hcoords⟩ := exists_nilpotent_conjugation_coordinate_bound
    dynkin Exp hExp chart hchart hc b u v
  let C := B * (A + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n s t hst
  let d := Exp ((n : ℝ) • v)
  have hprod : Exp (s • u) * Exp ((t - s) • u) = Exp (t • u) := by
    rw [← hExp.map_add_smul, show s + (t - s) = t by ring]
  have hdiff : (Exp (s • u))⁻¹ * Exp (t • u) = Exp ((t - s) • u) := by
    rw [← hprod, inv_mul_cancel_left]
  have hrel : (κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d) =
      κ (Exp (-(n : ℝ) • v) * Exp ((t - s) • u) * d) := by
    rw [← map_inv, ← map_mul, mul_inv_rev]
    have hd : d⁻¹ = Exp (-(n : ℝ) • v) := by
      dsimp [d]
      rw [neg_smul, hExp.map_neg]
    rw [hd]
    simpa only [mul_assoc] using congrArg (fun q => κ (Exp (-(n : ℝ) • v) * q * d)) hdiff
  have hdist : dist (κ (Exp (s • u) * d)) (κ (Exp (t • u) * d)) =
      dist 1 ((κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d)) := by
    simpa only [mul_one, mul_inv_cancel_left] using
      dist_mul_left (κ (Exp (s • u) * d)) (1 : G)
        ((κ (Exp (s • u) * d))⁻¹ * κ (Exp (t • u) * d))
  rw [hdist, hrel]
  let g := Exp (-(n : ℝ) • v) * Exp ((t - s) • u) * d
  have hg : Φ (b.equivFun (chart.symm g)) = κ g := by
    simp only [Φ, b.equivFun.symm_apply_apply]
    rw [← hchart, chart.apply_symm_apply]
  have hm := hmetric (b.equivFun (chart.symm g))
  rw [hg] at hm
  have hc' := hcoords n (t - s) hst
  change ‖b.equivFun (chart.symm g)‖ ≤ A * (1 + n) ^ c * |t - s| at hc'
  apply hm.trans
  have hBA : B * A ≤ C := by dsimp [C]; nlinarith
  have hBC : B ≤ C := by dsimp [C]; nlinarith
  have hp : 0 ≤ (1 + (n : ℝ)) ^ c := by positivity
  calc
    _ ≤ B * (1 + A * (1 + (n : ℝ)) ^ c * |t - s|) := by gcongr
    _ ≤ C * (1 + (n : ℝ)) ^ c * |t - s| + C := by
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBA hp) (abs_nonneg (t - s))]

end PolycyclicRecognition

end

end OAI
