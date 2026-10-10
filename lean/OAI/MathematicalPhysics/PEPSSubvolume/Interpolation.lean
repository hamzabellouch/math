import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators

namespace OAI

/-! Three-lines tangent estimates for entropy derivatives. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open Filter Topology
open PolynomialPEPS.PinnedEntropy

open Set Filter Complex Complex.HadamardThreeLines
open scoped Topology

namespace PolynomialPEPS.Subvolume.FilterInterpolation

theorem deriv_le_of_right_comparison {f g : ℝ → ℝ} {f' g' : ℝ}
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0)
    (hzero : f 0 = g 0) (hfg : ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ g x) :
    f' ≤ g' := by
  have hfl := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have hgl := (hasDerivAt_iff_tendsto_slope_left_right.mp hg).2
  apply le_of_tendsto_of_tendsto hfl hgl
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with x hx hx1
  simp only [mem_Ioi] at hx
  simp only [slope_def_field, sub_zero]
  apply div_le_div_of_nonneg_right _ (le_of_lt hx)
  rw [hzero]
  exact sub_le_sub_right (hfg x ⟨le_of_lt hx, le_of_lt hx1⟩) (g 0)

theorem threeLines_tangent_zero {f : ℂ → ℂ} {d : ℂ} {N : ℝ}
    (hN : 0 < N) (hzero : f 0 = 1) (hderiv : HasDerivAt f d 0)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ re ⁻¹' {0}, ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ re ⁻¹' {1}, ‖f z‖ ≤ N) :
    d.re ≤ Real.log N := by
  have hf : HasDerivAt (fun x : ℝ => (f x).re) d.re 0 := by
    simpa using hderiv.real_of_complex
  have hg : HasDerivAt (fun x : ℝ => Real.exp (x * Real.log N)) (Real.log N) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log N)).exp using 1 <;> simp
  apply deriv_le_of_right_comparison hf hg
  · simp [hzero]
  · intro x hx
    have hz : (x : ℂ) ∈ verticalClosedStrip 0 1 := by simpa [verticalClosedStrip] using hx
    have hbound := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      f hz hd hB hleft hright
    have habs : (f x).re ≤ ‖f x‖ := Complex.re_le_norm _
    refine habs.trans (hbound.trans_eq ?_)
    simp only [Complex.ofReal_re, Real.one_rpow, one_mul]
    rw [Real.rpow_def_of_pos hN]
    congr 1
    ring

theorem entropy_cost_upper_of_spectral_curve {f : ℂ → ℂ} {S N : ℝ}
    (hN : 0 < N) (hzero : f 0 = 1)
    (hderiv : HasDerivAt f ((-S / 2 : ℝ) : ℂ) 0)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (hleft : ∀ z ∈ re ⁻¹' {0}, ‖f z‖ ≤ 1)
    (hright : ∀ z ∈ re ⁻¹' {1}, ‖f z‖ ≤ N) :
    -Real.log (N ^ 2) ≤ S := by
  have h := threeLines_tangent_zero hN hzero hderiv hd hB hleft hright
  simp only [Complex.ofReal_re] at h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

end PolynomialPEPS.Subvolume.FilterInterpolation

end

end OAI
