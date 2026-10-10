import OAI.Geometry.RCD.Harmonic.WeightedAffinePotential

namespace OAI

/-! # Weighted scalar composition without an L² constant function -/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem centeredLipschitz {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b) :
    LipschitzWith D (fun a => b a-b 0) := by
  simpa only [add_zero] using hb.sub (LipschitzWith.const (b 0))

def weightedAffineComposition (θ : Lp ℝ ∞ μ) (w : Lp ℝ 2 μ)
    {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  lpMultiplier μ θ ((centeredLipschitz hb).compLp (sub_self _) f)+b 0 • w

theorem weightedAffineComposition_coe (θ : Lp ℝ ∞ μ) (w : Lp ℝ 2 μ)
    (hθ : θ =ᵐ[μ] w) {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b)
    (f : Lp ℝ 2 μ) : weightedAffineComposition μ θ w hb f =ᵐ[μ]
      fun x => θ x*b (f x) := by
  filter_upwards [Lp.coeFn_add (lpMultiplier μ θ ((centeredLipschitz hb).compLp (sub_self _) f))
    (b 0 • w), lpMultiplier_coe μ θ ((centeredLipschitz hb).compLp (sub_self _) f),
    (centeredLipschitz hb).coeFn_compLp (sub_self _) f,Lp.coeFn_smul (b 0) w,hθ]
    with x ha hp hf hs hθx
  change (lpMultiplier μ θ ((centeredLipschitz hb).compLp (sub_self _) f)+b 0 • w) x = _
  simp only [ha,Pi.add_apply,hp,hf,Function.comp_apply,hs,Pi.smul_apply,smul_eq_mul,hθx]
  ring

theorem weightedAffineComposition_sub_norm_le (θ : Lp ℝ ∞ μ) (w : Lp ℝ 2 μ)
    {b : ℝ → ℝ} {D : ℝ≥0} (hb : LipschitzWith D b) (f g : Lp ℝ 2 μ) :
    ‖weightedAffineComposition μ θ w hb f-weightedAffineComposition μ θ w hb g‖ ≤
      ‖lpMultiplier μ θ‖*D*‖f-g‖ := by
  have he : weightedAffineComposition μ θ w hb f-weightedAffineComposition μ θ w hb g =
      lpMultiplier μ θ ((centeredLipschitz hb).compLp (sub_self _) f-
        (centeredLipschitz hb).compLp (sub_self _) g) := by
    simp only [weightedAffineComposition,map_sub]
    abel
  rw [he]
  exact ((lpMultiplier μ θ).le_opNorm _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((centeredLipschitz hb).norm_compLp_sub_le (sub_self _) f g) (norm_nonneg _))

end RegularPointCoordinates

end

end OAI
