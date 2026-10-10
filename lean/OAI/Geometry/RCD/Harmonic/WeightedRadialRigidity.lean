import OAI.Geometry.RCD.Transport.RadialMidpointRigidity

namespace OAI

/-! # Cost rigidity for a radial split at any interior time -/

open Set Filter Metric MeasureTheory

namespace RegularPointCoordinates

theorem weighted_radial_defect_nonneg {a d e f : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (htri : f ≤ d + e) :
    0 ≤ (1 - a) * d ^ 2 + a * e ^ 2 - a * (1 - a) * f ^ 2 := by
  have hh : 0 ≤ a * (1 - a) * ((d + e) ^ 2 - f ^ 2) :=
    mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (by nlinarith)
  nlinarith [sq_nonneg ((1 - a) * d - a * e)]

theorem weighted_radial_defect_zero {a d e f : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (htri : f ≤ d + e)
    (hz : (1 - a) * d ^ 2 + a * e ^ 2 - a * (1 - a) * f ^ 2 = 0) :
    d = a * f ∧ e = (1 - a) * f ∧ f = d + e := by
  have hprod : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha1)
  have hdiff : 0 ≤ (d + e) ^ 2 - f ^ 2 := by nlinarith
  have hs : ((1 - a) * d - a * e) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((1 - a) * d - a * e), mul_nonneg hprod.le hdiff]
  have heq : (1 - a) * d = a * e := by nlinarith
  have hsq : (d + e) ^ 2 = f ^ 2 := by
    have hh : a * (1 - a) * ((d + e) ^ 2 - f ^ 2) = 0 := by nlinarith [hs]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hprod.ne')
  have hfde : f = d + e := by nlinarith
  exact ⟨by nlinarith [hfde], by nlinarith [hfde], hfde⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem weighted_radial_rigidity_of_moments (π : Measure C(Time, X)) (p : X)
    {a C : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hD : Integrable (fun γ : C(Time, X) => dist (γ 0) (γ 1) ^ 2) π)
    (h0 : Integrable (fun γ : C(Time, X) => dist (γ 0) p ^ 2) π)
    (h1 : Integrable (fun γ : C(Time, X) => dist (γ 1) p ^ 2) π)
    (hcost : (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π) ≤ a ^ 2 * C)
    (hm0 : (∫ γ, dist (γ 0) p ^ 2 ∂π) = C)
    (hm1 : (∫ γ, dist (γ 1) p ^ 2 ∂π) = (1 - a) ^ 2 * C) :
    ∀ᵐ γ ∂π, dist (γ 0) (γ 1) = a * dist (γ 0) p ∧
      dist (γ 1) p = (1 - a) * dist (γ 0) p ∧
      dist (γ 0) p = dist (γ 0) (γ 1) + dist (γ 1) p := by
  let F := fun γ : C(Time, X) => (1 - a) * dist (γ 0) (γ 1) ^ 2 +
    a * dist (γ 1) p ^ 2 - a * (1 - a) * dist (γ 0) p ^ 2
  have hi : Integrable F π := ((hD.const_mul (1 - a)).add (h1.const_mul a)).sub
    (h0.const_mul (a * (1 - a)))
  have hn : ∀ᵐ γ ∂π, 0 ≤ F γ := Eventually.of_forall fun γ =>
    weighted_radial_defect_nonneg ha.le ha1.le dist_nonneg dist_nonneg dist_nonneg
      (dist_triangle (γ 0) (γ 1) p)
  have hz : (∫ γ, F γ ∂π) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hn)
    have hh := mul_le_mul_of_nonneg_left hcost (sub_nonneg.mpr ha1.le)
    dsimp only [F]
    have hiadd : Integrable (fun γ : C(Time, X) =>
        (1 - a) * dist (γ 0) (γ 1) ^ 2 + a * dist (γ 1) p ^ 2) π :=
      (hD.const_mul (1 - a)).add (h1.const_mul a)
    rw [integral_sub hiadd (h0.const_mul _)]
    have haadd : Integrable (fun γ : C(Time, X) => (1 - a) * dist (γ 0) (γ 1) ^ 2) π :=
      hD.const_mul (1 - a)
    have hbadd : Integrable (fun γ : C(Time, X) => a * dist (γ 1) p ^ 2) π := h1.const_mul a
    rw [integral_add haadd hbadd, integral_const_mul, integral_const_mul, integral_const_mul,
      hm0, hm1]
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [hae] with γ hγ
  change F γ = 0 at hγ
  exact weighted_radial_defect_zero ha ha1 dist_nonneg dist_nonneg dist_nonneg
    (dist_triangle (γ 0) (γ 1) p) hγ

end RegularPointCoordinates

end OAI
