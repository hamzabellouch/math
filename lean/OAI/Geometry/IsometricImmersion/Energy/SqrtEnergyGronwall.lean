import OAI.Geometry.IsometricImmersion.Energy.MovingHyperbolicEnergy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Hyperbolic

theorem regularized_sqrt_rate_le
    {E Ed force C eta : ℝ} (hE : 0 ≤ E) (hforce : 0 ≤ force) (hC : 0 ≤ C)
    (heta : 0 < eta) (hEd : Ed ≤ C * E + Real.sqrt (2 * E) * force) :
    Ed / (2 * Real.sqrt (E + eta)) ≤ C * Real.sqrt (E + eta) + force := by
  have hpos : 0 < E + eta := by linarith
  have hrootpos := Real.sqrt_pos.2 hpos
  have hsquare := Real.sq_sqrt hpos.le
  have hroot : Real.sqrt (2 * E) ≤ 2 * Real.sqrt (E + eta) := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (E + eta))).2
  have hf := mul_le_mul_of_nonneg_right hroot hforce
  have hCE : C * E ≤ 2 * C * (E + eta) := by
    nlinarith [mul_nonneg hC hE, mul_nonneg hC heta.le]
  nlinarith

def regularizedWeightedEnergy (E : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) * Real.sqrt (E t + eta)

def regularizedWeightedRate (E Ed : ℝ → ℝ) (C a eta : ℝ) (t : ℝ) : ℝ :=
  Real.exp (-C * (t - a)) *
    (Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))

theorem regularizedWeightedEnergy_hasDerivAt
    {E : ℝ → ℝ} {Ed C a eta t : ℝ} (hd : HasDerivAt E Ed t)
    (hE : 0 ≤ E t) (heta : 0 < eta) :
    HasDerivAt (regularizedWeightedEnergy E C a eta)
      (Real.exp (-C * (t - a)) *
        (Ed / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta))) t := by
  have hroot := (hd.add_const eta).sqrt (by linarith : E t + eta ≠ 0)
  have he := (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp
  have hh := he.mul hroot
  simp only [id_eq, mul_one] at hh
  unfold regularizedWeightedEnergy
  convert hh using 1
  first | rfl | ring

theorem regularizedWeightedRate_le
    {E Ed force : ℝ → ℝ} {C a eta t : ℝ} (hE : 0 ≤ E t)
    (hforce : 0 ≤ force t) (hC : 0 ≤ C) (heta : 0 < eta) (hat : a ≤ t)
    (hEd : Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    regularizedWeightedRate E Ed C a eta t ≤ force t := by
  have hy := regularized_sqrt_rate_le hE hforce hC heta hEd
  have hfactor : Real.exp (-C * (t - a)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    nlinarith
  have hfpos := (Real.exp_pos (-C * (t - a))).le
  have hmul := mul_le_mul_of_nonneg_left (show
    Ed t / (2 * Real.sqrt (E t + eta)) - C * Real.sqrt (E t + eta) ≤ force t by linarith) hfpos
  exact hmul.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hforce])

theorem regularized_sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b eta : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C) (heta : 0 < eta)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b + eta) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t) := by
  have hwcont : ContinuousOn (regularizedWeightedEnergy E C a eta) (Icc a b) := by
    exact (show Continuous (fun t : ℝ => Real.exp (-C * (t - a))) by fun_prop).continuousOn.mul
      ((hEcont.add continuousOn_const).sqrt)
  have hwderiv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivWithinAt (regularizedWeightedEnergy E C a eta)
        (regularizedWeightedRate E Ed C a eta t) (Ioi t) t :=
    (regularizedWeightedEnergy_hasDerivAt (hderiv t ht)
      (hE t ⟨ht.1.le, ht.2.le⟩) heta).hasDerivWithinAt
  have hint := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hwcont hwderiv
    (hforce.integrableOn_compact isCompact_Icc) (fun t ht =>
      regularizedWeightedRate_le (hE t ⟨ht.1.le, ht.2.le⟩)
        (hforcepos t ⟨ht.1.le, ht.2.le⟩) hC heta ht.1.le (hineq t ht))
  have hw : Real.exp (-C * (b - a)) * Real.sqrt (E b + eta) ≤
      Real.sqrt (E a + eta) + ∫ t in a..b, force t := by
    simpa only [regularizedWeightedEnergy, sub_self, mul_zero, Real.exp_zero, one_mul,
      sub_le_iff_le_add, add_comm] using hint
  have hmul := mul_le_mul_of_nonneg_left hw (Real.exp_pos (C * (b - a))).le
  have hexp : Real.exp (C * (b - a)) * Real.exp (-C * (b - a)) = 1 := by
    rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
  simpa only [← mul_assoc, hexp, one_mul] using hmul

theorem sqrt_energy_gronwall
    {E Ed force : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hEcont : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt E (Ed t) t)
    (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (hforce : ContinuousOn force (Icc a b))
    (hforcepos : ∀ t ∈ Icc a b, 0 ≤ force t)
    (hC : 0 ≤ C)
    (hineq : ∀ t ∈ Ioo a b, Ed t ≤ C * E t + Real.sqrt (2 * E t) * force t) :
    Real.sqrt (E b) ≤ Real.exp (C * (b - a)) *
      (Real.sqrt (E a) + ∫ t in a..b, force t) := by
  have ht0 : Tendsto (fun eta : ℝ => eta) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousWithinAt_id.tendsto
  have hleft : Tendsto (fun eta : ℝ => Real.sqrt (E b + eta))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (E b))) := by
    simpa only [add_zero] using (tendsto_const_nhds.add ht0).sqrt
  have hright : Tendsto (fun eta : ℝ => Real.exp (C * (b - a)) *
      (Real.sqrt (E a + eta) + ∫ t in a..b, force t)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (C * (b - a)) * (Real.sqrt (E a) + ∫ t in a..b, force t))) := by
    simpa only [add_zero] using tendsto_const_nhds.mul
      (((tendsto_const_nhds.add ht0).sqrt).add tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact regularized_sqrt_energy_gronwall hab hEcont hderiv hE hforce hforcepos hC heta hineq

end SmoothLocal.Hyperbolic

end

end OAI
