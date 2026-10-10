import OAI.Geometry.RCD.Sobolev.HarmonicGradientConstruction

namespace OAI

/-! # Uniform bounds for the actual rescaled harmonic energy density -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_scaled_energy_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S R : ℝ} (hS : 0<S) (hR : 0≤R) (hRS : R<S)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hcurv : ∀ k, -1≤K*r k^2)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (p k) (S*r k)) (w k))
    (hnorm : ∀ k, harmonicTargetNorm hX (p k) (S*r k) (w k)≤1) :
    ∃ M : ℝ, 0≤M ∧ ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M := by
  let T := (R+S)/2
  have hT : 0<T := by dsimp [T]; linarith
  have hRT : R<T := by dsimp [T]; linarith
  have hTS : T<S := by dsimp [T]; linarith
  obtain ⟨G,_,hG⟩ := hX.harmonicGradientInput hn (p 0) hn (S^2) (T/S)
    (sq_nonneg _) (div_pos hT hS) ((div_lt_one hS).mpr hTS)
  refine ⟨(G/S)^2,sq_nonneg _,?_⟩
  intro k
  have hK : -(S^2)≤K*(S*r k)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left (hcurv k) (sq_nonneg S)]
  have he := hG (p k) (S*r k) (mul_pos hS (hr k)) hK (w k) (hw k)
  have hmean := sobolev_mean_sq_le_one_of_normalized (hausdorff n X) hX.quadratic
    (ball (p k) (S*r k)) (hX.finiteOnBounded _ isBounded_ball).ne (w k) (hnorm k)
  have ht : (T/S)*(S*r k)=T*r k := by field_simp
  rw [ht,ae_restrict_iff' measurableSet_ball] at he
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem measurableSet_closedBall] with x hx hdist
  have hxT : x∈ball (p k) (T*r k) :=
    lt_of_le_of_lt hdist (mul_lt_mul_of_pos_right hRT (hr k))
  have hb := (hx hxT).trans (mul_le_mul_of_nonneg_left hmean (sq_nonneg (G/(S*r k))))
  calc r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x
      ≤r k^2*(G/(S*r k))^2 := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hb (sq_nonneg (r k))
    _ = (G/S)^2 := by field_simp [hS.ne',(hr k).ne']

end RegularPointCoordinates

end

end OAI
