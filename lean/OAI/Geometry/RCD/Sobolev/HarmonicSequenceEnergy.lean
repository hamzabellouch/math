import OAI.Geometry.RCD.Sobolev.HarmonicInteriorEnergy
import OAI.Geometry.RCD.Harmonic.HarmonicAffineSequence

namespace OAI

/-! # Discharging the local energy hypothesis of harmonic compactness -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
/-- The gradient estimate supplies all the rescaled interior
H¹ bounds required by harmonic compactness, uniformly along the sequence. -/
theorem rescaled_harmonic_energy_of_gradient {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {S : ℝ} (hS : 0 < S) (p : ℕ → X) (r : ℕ → ℝ)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K * r k ^ 2)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (p k) (S * r k)) (w k))
    (hnorm : ∀ k, ‖normalizeLocalL2 (hausdorff n X) (ball (p k) (S * r k))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (p k) (S * r k)) (w k))‖ ≤ 1) :
    ∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      r k ^ 2 * ((hausdorff n X).real (ball (p k) (S * r k)))⁻¹ *
        (∫ x in ball (p k) (ρ * r k), localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X) ≤ C := by
  intro ρ hρ hρS
  obtain ⟨C, hC, hbound⟩ := hinput.interior_energy hn (sq_nonneg S)
    (div_pos hρ hS) ((div_lt_one hS).mpr hρS)
  refine ⟨C ^ 2 / S ^ 2, by positivity, ?_⟩
  intro k
  have hcurv' : -(S ^ 2) ≤ K * (S * r k) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left (hcurv k) (sq_nonneg S)
    convert hm using 1 <;> ring
  have hb := hbound (p k) (S * r k) (mul_pos hS (hr k)) hcurv' (w k) (hw k) (hnorm k)
  have hradius : ρ / S * (S * r k) = ρ * r k := by field_simp
  rw [hradius] at hb
  have hh := div_le_div_of_nonneg_right hb (sq_nonneg S)
  convert hh using 1
  field_simp

end RegularPointCoordinates

end

end OAI
