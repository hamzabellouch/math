import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # Signed radial exponential weights for the Davies estimate

Both signs of the bounded distance weight are needed when the two
half-time density rows are paired. No heat-kernel estimate is assumed.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radialWeight_signed_bound (p : X) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) (x : X) :
    |radialWeight p a R x| ≤ Real.exp (|a| *R) := by
  rw [abs_of_nonneg (radialWeight_nonneg p a R x)]
  apply Real.exp_le_exp.mpr
  have hm : 0 ≤ min (dist p x) R := le_min dist_nonneg hR
  exact (mul_le_mul_of_nonneg_right (le_abs_self a) hm).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg a))

theorem radialWeight_signed_lipschitz (p : X) (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith ⟨|a| *Real.exp (|a| *R), by positivity⟩ (radialWeight p a R) := by
  have hmin := (LipschitzWith.dist_right p).min_const R
  have hl := lipschitzWith_const_mul_real hmin a
  have hex : LipschitzOnWith ⟨Real.exp (|a| *R), (Real.exp_pos _).le⟩ Real.exp (Iic (|a| *R)) := by
    apply (convex_Iic _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    change |Real.exp x| ≤ Real.exp (|a| *R)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  have hub (x : X) : a*min (dist p x) R ≤ |a| *R := by
    have hm : 0 ≤ min (dist p x) R := le_min dist_nonneg hR
    exact (mul_le_mul_of_nonneg_right (le_abs_self a) hm).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg a))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hex.dist_le_mul _ (hub x) _ (hub y)
  have hv := mul_le_mul_of_nonneg_left (hl.dist_le_mul x y) (Real.exp_pos (|a| *R)).le
  simp only [coe_nnnorm,Real.norm_eq_abs,mul_one] at hv
  exact hh.trans (by
    change Real.exp (|a| *R)*dist (a*min (dist p x) R) (a*min (dist p y) R) ≤
      |a| *Real.exp (|a| *R)*dist x y
    nlinarith only [hv])

theorem radialWeight_signed_slope (p : X) (a R : ℝ) (x : X) :
    localSlope (radialWeight p a R) x ≤ ENNReal.ofReal (|a| *radialWeight p a R x) := by
  let u := fun x => a*min (dist p x) R
  have hu : LipschitzWith ‖a‖₊ u := by
    simpa only [mul_one] using lipschitzWith_const_mul_real ((LipschitzWith.dist_right p).min_const R) a
  have hs := localSlope_comp_hasDerivAt (Real.hasDerivAt_exp (u x)) hu.continuous.continuousAt
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hu x))
  change localSlope (radialWeight p a R) x ≤ _ at hs
  rw [abs_of_pos (Real.exp_pos _)] at hs
  apply hs.trans
  calc
    _ ≤ ENNReal.ofReal (radialWeight p a R x)*ENNReal.ofReal |a| := by
      apply mul_le_mul' le_rfl
      have he : ENNReal.ofReal |a| = (‖a‖₊ : ℝ≥0∞) := by
        rw [← Real.norm_eq_abs, ofReal_norm, enorm_eq_nnnorm]
      rw [he]
      exact localSlope_le_of_lipschitz hu x
    _ = _ := by rw [← ENNReal.ofReal_mul (radialWeight_nonneg p a R x)]; congr 1; ring

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_signed_radialWeight_integral (f : Lp ℝ 2 μ) (p : X)
    (a : ℝ) {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) :
    Integrable (fun x => radialWeight p a R x*(heatAt μ hQ t f x)^2) μ ∧
    (∫ x, radialWeight p a R x*(heatAt μ hQ t f x)^2 ∂μ) ≤
      Real.exp (a^2/2*t)*(∫ x, radialWeight p a R x*(f x)^2 ∂μ) := by
  have hv := radialWeight_signed_lipschitz p a hR
  let B : ℝ≥0 := ⟨Real.exp (|a| *R), (Real.exp_pos _).le⟩
  have hb (x : X) : |radialWeight p a R x| ≤ B := radialWeight_signed_bound p a hR x
  let V := boundedMultiplier μ (radialWeight p a R) hv.continuous.measurable B hb
  have hV : V =ᵐ[μ] radialWeight p a R := boundedMultiplier_coe μ _ _ _ _
  have hh := heatAt_weighted_bound μ hQ f hv (Real.exp (a*R))
    (radialWeight_constant_outside p a R) hb (radialWeight_nonneg p a R)
    V hV (abs_nonneg a) (radialWeight_signed_slope p a R) ht
  have hi := lpMultiplier_integral_sq μ V (heatAt μ hQ t f) hV
  have hi0 := lpMultiplier_integral_sq μ V f hV
  rw [hi.2,hi0.2,sq_abs] at hh
  exact ⟨hi.1,hh⟩

end RegularPointCoordinates

end

end OAI
