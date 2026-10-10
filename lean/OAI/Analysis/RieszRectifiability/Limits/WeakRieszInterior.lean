import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RieszInteriorCapError
import OAI.Analysis.RieszRectifiability.Limits.FiniteWeakProducts

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem cappedRieszInterior_integral_tendsto {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (e : Ambient d) (φ : Ambient d → ℝ) (hφ : Continuous φ)
    (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun j => ∫ q, cappedRieszInterior m ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, cappedRieszInterior m ε e φ q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let Q := (2 * (B : ℝ) * ‖e‖) * (ε ^ m)⁻¹
  let F : Ambient d × Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨cappedRieszInterior m ε e φ, cappedRieszInterior_continuous m ε hε e φ hφ⟩
    (2 * Q) (by
      intro q z
      change dist (cappedRieszInterior m ε e φ q) (cappedRieszInterior m ε e φ z) ≤ 2 * Q
      rw [Real.dist_eq]
      have ht := abs_sub_le (cappedRieszInterior m ε e φ q) 0 (cappedRieszInterior m ε e φ z)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      have hq := cappedRieszInterior_bound m ε hε e φ B hB q
      have hz := cappedRieszInterior_bound m ε hε e φ B hB z
      dsimp only [Q]
      linarith)
  exact finiteMeasure_bounded_product_integral_tendsto μ μ ν ν hweak hweak hν hν F

theorem rieszInterior_integral_tendsto_of_weak {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hgν : GlobalUpperGrowth (p + 1) C (ν : Measure (Ambient d)))
    (M : ℝ) (hM : ∀ j, (μ j : Measure (Ambient d)).real univ ≤ M)
    (e : Ambient d) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, rieszInteriorIntegrand (p + 1) e φ q
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  let N := max M ((ν : Measure (Ambient d)).real univ)
  have hN : 0 ≤ N := measureReal_nonneg.trans (le_max_right _ _)
  have hC : 0 ≤ C := hgν.1
  let A := (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p)))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsource (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))| ≤ A * ε := by
    have hb := (rieszInterior_integrable_and_cap_error p C (μ j : Measure (Ambient d))
      (hg j) e φ L B hφ hB ε hε).2
    apply hb.trans
    calc
      _ ≤ (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right ((hM j).trans (le_max_left _ _)) (by positivity))
          (by positivity)
      _ = _ := by dsimp only [A]; ring
  have htarget (ε : ℝ) (hε : 0 < ε) :
      |(∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) -
        ∫ q, cappedRieszInterior (p + 1) ε e φ q
          ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))| ≤ A * ε := by
    have hb := (rieszInterior_integrable_and_cap_error p C (ν : Measure (Ambient d))
      hgν e φ L B hφ hB ε hε).2
    apply hb.trans
    calc
      _ ≤ (‖e‖ * (L : ℝ)) * (N * (2 * (C * 2 ^ (p + 1) * 2 ^ p * ε))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)
      _ = _ := by dsimp only [A]; ring
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let ε := η / (3 * (A + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have heq : (3 * (A + 1)) * ε = η := by
    dsimp only [ε]
    field_simp
  have hsmall : A * ε < η / 3 := by nlinarith
  have hthird : 0 < η / 3 := by positivity
  have hcap := cappedRieszInterior_integral_tendsto (p + 1) μ ν hweak hν e φ hφ.continuous B hB ε hε
  filter_upwards [Metric.tendsto_nhds.mp hcap (η / 3) hthird] with j hj
  have hjerr := (hsource j ε hε).trans_lt hsmall
  have hνerr := (htarget ε hε).trans_lt hsmall
  rw [← Real.dist_eq] at hjerr hνerr
  have ht := dist_triangle
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
  have ht' := dist_triangle
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d)))
    (∫ q, cappedRieszInterior (p + 1) ε e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
    (∫ q, rieszInteriorIntegrand (p + 1) e φ q
      ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))
  rw [dist_comm] at hνerr
  linarith

end

end RieszRectifiability

end OAI
