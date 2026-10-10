import OAI.Geometry.RCD.Sobolev.HarmonicInteriorEnergy

namespace OAI

/-! # Uniform local energy for dimensionless harmonic sequences -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The physical radius is `S * r`, while the compactness energy is
normalized by `r²`. The interior estimate supplies the required
bound uniformly over every center and every admissible radius. -/
theorem LocalHarmonicL2GradientInput.rescaled_interior_energy {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {S ρ : ℝ} (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K * r ^ 2 →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (S * r)) w →
        ‖normalizeLocalL2 (hausdorff n X) (ball p (S * r))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
          (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (S * r)) w)‖ ≤ 1 →
        r ^ 2 * ((hausdorff n X).real (ball p (S * r)))⁻¹ *
          (∫ x in ball p (ρ * r), localGamma (hausdorff n X) hX.quadratic w w x
            ∂hausdorff n X) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hinput.interior_energy hn (sq_nonneg S)
    (div_pos hρ hS) ((div_lt_one hS).mpr hρS)
  refine ⟨C ^ 2 / S ^ 2, by positivity, ?_⟩
  intro p r hr hcurv w hw hnorm
  have hcurv' : -(S ^ 2) ≤ K * (S * r) ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left hcurv (sq_nonneg S)
    nlinarith only [hc]
  have hh := hbound p (S * r) (mul_pos hS hr) hcurv' w hw hnorm
  have hradius : ρ / S * (S * r) = ρ * r := by field_simp
  rw [hradius] at hh
  apply (le_div_iff₀ (sq_pos_of_pos hS)).mpr
  convert hh using 1; ring

end RegularPointCoordinates

end

end OAI
