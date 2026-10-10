import OAI.Geometry.RCD.Heat.HeatGamma

namespace OAI

/-! # Constructing the Sobolev energy density of heat-regularized tests -/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_compact_energy_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {t : ℝ} (ht : 0 < t) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        (fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) x) ^ 2) ∧
      ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x| ≤
        ((L : ℝ) * Real.exp (-K * t)) ^ 2 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let F := heatSobolev μ hX.quadratic t ht f
  have hm := hX.heat_compact_gamma_memLp K n hn hφ hs p f hf t ht
  let H := hm.toLp (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2)
  have hH : (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2) =ᵐ[μ] H :=
    hm.coeFn_toLp.symm
  let C : ℝ≥0 := ⟨((L : ℝ) * Real.exp (-K * t)) ^ 2, sq_nonneg _⟩
  have hC : ∀ᵐ x ∂μ, |H x| ≤ C := by
    have hb := hX.heat_compact_slope_bdd K n hn hφ hs p f hf t ht
    have h0 := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic F)
    filter_upwards [hH, hb, h0] with x hx hb' h0'
    rw [← hx, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0' hb' 2
  have hfinite := hX.heat_gamma_finite_energy hn p f ht H C hH hC
  let G : SobolevSpace μ hX.quadratic := ⟨H, hfinite⟩
  exact ⟨G, hH.symm, hC⟩

end RegularPointCoordinates

end

end OAI
