import OAI.Geometry.SurfaceImmersion.Geometry.AxisNormalizedDefect

namespace OAI

/-! The normalized endpoint jets retain nonzero transverse normal components. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisNormalizedDefect_derivative_bijective {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x)
    (hx : d (x 1) ≠ 0) (hz : N x = 0) (hD : Function.Bijective (fderiv ℝ N x)) :
    Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) x) := by
  rw [axisNormalizedDefect_fderiv_zero hd hN hx hz]
  exact (planeComplexFrame_invertible hx).inverse.bijective.comp hD

lemma normalized_axis_derivative {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) :
    fderiv ℝ G (crosscapAxis t) (![0,1] : Base) = ![(t-p)+(t-q),0] := by
  have he : G ∘ crosscapAxis =ᶠ[𝓝 t] fun s => (![(s-p)*(s-q),0] : Base) := by
    filter_upwards [hW.mem_nhds ht] with s hs
    exact haxis s hs
  have hd := (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hp : HasDerivAt (fun s : ℝ => (![(s-p)*(s-q),0] : Base))
      (![(t-p)+(t-q),0] : Base) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((hasDerivAt_id t).sub_const p).mul ((hasDerivAt_id t).sub_const q) using 1 <;> simp [add_comm]
      rfl
    · exact hasDerivAt_const t 0
  have hj := he.deriv_eq.trans hp.deriv
  exact (by simpa only [crosscapAxis_apply] using hd.deriv.symm.trans hj)

lemma normalized_axis_transverse_nonzero {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0])
    (hD : Function.Bijective (fderiv ℝ G (crosscapAxis t))) :
    (fderiv ℝ G (crosscapAxis t) (![1,0] : Base)) 1 ≠ 0 := by
  apply injective_second_column_nonzero _ hD.2
  rw [normalized_axis_derivative hG hW ht haxis]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
