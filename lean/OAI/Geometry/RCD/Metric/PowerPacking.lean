import OAI.Geometry.RCD.Metric.NearbySmallBallMass
import OAI.Geometry.RCD.Coordinates.PatchCover

namespace OAI

/-! # The exact dimensional power in the RCD packing bound

Unlike a bound obtained by repeated doubling, the exponent here is exactly
n. This is needed to exclude an extra geodesic factor in an n-dimensional
almost splitting.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.power_packing_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {R d : ℝ}
    (hR : 0 < R) (hd : 0 < d) (hdR : d ≤ R) (hcurv : -1 ≤ K*(4*R)^2)
    (s : Finset X) (hnear : ∀ x ∈ s, dist x p ≤ R)
    (hsep : (s : Set X).Pairwise (fun x y => d ≤ dist x y)) :
    (s.card:ℝ)*d^n ≤ (Real.cosh 1^(n-1)*8^n)*R^n := by
  let μ := hausdorff n X
  let M := μ.real (ball p (2*R))
  let A := (Real.cosh 1^(n-1)*2^n)*(2*R)^n
  have hM : 0 < M := ENNReal.toReal_pos
    (hX.fullSupport p (2*R) (by positivity)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hA : 0 < A := by dsimp only [A]; positivity
  have hlower (x : X) (hx : x ∈ s) : M*(d/2)^n/A ≤ μ.real (ball x (d/2)) := by
    apply (div_le_iff₀ hA).mpr
    have hh := hX.nearby_small_ball_mass hn (p := p) (z := x) (R := 2*R)
      (r := d/2) (by positivity) (by linarith [hnear x hx]) (by positivity)
      (by linarith) (by simpa only [show 2*(2*R)=4*R by ring] using hcurv)
    simpa only [M,A,mul_comm] using hh
  have hcard := separated_card_mul_volume_le μ s p hsep hnear hlower
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hupper : μ.real (ball p (R+d/2)) ≤ M :=
    measureReal_mono (ball_subset_ball (by linarith)) (hX.finiteOnBounded _ isBounded_ball).ne
  have hc := hcard.trans hupper
  have hc' : ((s.card:ℝ)*(d/2)^n)*M ≤ A*M := by
    have hh := (div_le_iff₀ hA).mp (show (s.card:ℝ)*M*(d/2)^n/A ≤ M by
      convert hc using 1; ring)
    nlinarith only [hh]
  have hcancel := (mul_le_mul_iff_left₀ hM).mp hc'
  have htwo := mul_le_mul_of_nonneg_right hcancel (show 0 ≤ (2:ℝ)^n by positivity)
  calc
    (s.card:ℝ)*d^n = ((s.card:ℝ)*(d/2)^n)*2^n := by rw [mul_assoc,← mul_pow]; congr 1; ring
    _ ≤ A*2^n := htwo
    _ = _ := by
      dsimp only [A]
      rw [mul_pow]
      ring_nf
      rw [Nat.mul_comm n 3,pow_mul]
      norm_num

end RegularPointCoordinates

end

end OAI
