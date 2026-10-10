import OAI.Probability.InvariantIsing.Cavity.CavityDeficitGap
import OAI.Probability.InvariantIsing.Spectral.SpectralGroupRoots

namespace OAI

/-! The scalar field increments prescribed by the quadratic cavity
calculation are exactly the integrals defining the manuscript field path. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma continuousAt_deriv_finiteR_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (deriv (finiteR rho lam hrho hsum)) x := by
  have h1 := (hasStrictDerivAt_finiteInverseDerivative rho lam hrho hsum hx).hasDerivAt.continuousAt
  have h2 : ContinuousAt (fun y : ℝ => 1 / y ^ 2) x :=
    continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx.ne')
  apply (h1.add h2).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (hasStrictDerivAt_finiteR rho lam hrho hsum hy).hasDerivAt.deriv

/-- Positive-level covariance increments; no assumption about endpoint
atoms is needed, only that the open interval is a gap in the support. -/
theorem integral_finiteR_deriv_deficit_gap (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {a b : ℝ} (hab : a < b)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    (hpos : 0 < deficit p b) (hmass : pathMeasure.real {s | p s ≤ a} ≠ 0) :
    (∫ r in a..b, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p a) -
        finiteR rho lam hrho hsum (deficit p b)) / pathMeasure.real {s | p s ≤ a} := by
  let R := finiteR rho lam hrho hsum
  let ζ := pathMeasure.real {s | p s ≤ a}
  have hp (r : ℝ) (hr : r ∈ Icc a b) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => deriv R (deficit p r)) (Icc a b) := by
    intro r hr
    exact ((continuousAt_deriv_finiteR_pos rho lam hrho hsum (hp r hr)).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun r => deriv R (deficit p r)) volume a b :=
    ((uIcc_of_le hab.le).symm ▸ hc).intervalIntegrable
  have hcomp : ContinuousOn (fun r => R (deficit p r)) (Icc a b) := by
    intro r hr
    exact (((hasStrictDerivAt_finiteR rho lam hrho hsum (hp r hr)).hasDerivAt.continuousAt).comp
      (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo a b, HasDerivAt (fun r => R (deficit p r))
      ((-ζ) * deriv R (deficit p r)) r := by
    intro r hr
    have hR := (hasStrictDerivAt_finiteR rho lam hrho hsum
      (hp r ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    rw [← hR.deriv] at hR
    convert! hR.comp r hD using 1
    dsimp only [R, ζ]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcomp hd
    (hi.const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in a..b, deriv R (deficit p r)) * ζ = R (deficit p a) - R (deficit p b)
  linarith

/-- The common-root contribution includes the full interval below the
smallest overlap, on which the deficit is constant. -/
theorem integral_finiteR_deriv_deficit_root (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (p : OverlapPath) :
    (∫ r in 0..Function.rightLim p.val 0,
      deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      Function.rightLim p.val 0 * deriv (finiteR rho lam hrho hsum)
        (deficit p (Function.rightLim p.val 0)) := by
  calc
    _ = ∫ _r in 0..Function.rightLim p.val 0, deriv (finiteR rho lam hrho hsum)
        (deficit p (Function.rightLim p.val 0)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le p.rightLim_mem_unit.1
      intro r hr
      dsimp only
      rw [deficit_eq_at_rightLim_of_le p hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

end InvariantIsing

end

end OAI
