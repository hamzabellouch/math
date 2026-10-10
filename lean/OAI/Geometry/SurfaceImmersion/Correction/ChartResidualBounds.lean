import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartBounds

namespace OAI

/-! Transfer a residual estimate back through its phase chart and extend
it globally using the already established compact support. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open WeightedEstimates

lemma real_pullbackField_inverse {χ e : SmallModes.Base → SmallModes.Base} {x : SmallModes.Base}
    (hχ : DifferentiableAt ℝ χ x) (he : DifferentiableAt ℝ e (χ x))
    (hi : e ∘ χ =ᶠ[nhds x] id) (A : Tensor) :
    pullbackField χ x (pullbackField e (χ x) A) = A := by
  have hc := congrArg QuadraticMean.realPart
    (complexPullbackField_inverse hχ he hi (RealModes.complexify A))
  simpa only [complexPullbackField, realPart_complexPullback, realPart_complexify, pullbackField] using hc

lemma weighted_residual_from_chart
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {R : SmallModes.Base → Tensor} (hRs : tsupport R ⊆ e.source)
    {τ C J D : ℝ} {m : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hC : 0 ≤ C) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hcoords : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.source τ m D (SmallModes.coordDeriv v e))
    (hsm : ContDiffOn ℝ ∞ (fun y => pullbackField e.symm y (R (e.symm y))) e.target)
    (hb : WeightedBound e.target τ m C (fun y => pullbackField e.symm y (R (e.symm y)))) :
    WeightedBound Set.univ τ m (JetPolynomial.tensorChartBudget m J D * C) R := by
  have hc := hb.comp_coordinates e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hτ hτ1 hJ hC
    he hsm (fun _ hx => e.map_source hx) hcoords
  have hp := weighted_pullbackField_apply e.open_source hτ (by positivity) hD
    (hsm.comp he (fun _ hx => e.map_source hx)) he hc hfield
  have hid (x : SmallModes.Base) (hx : x ∈ e.source) :
      pullbackField e x (pullbackField e.symm (e x) (R (e.symm (e x)))) = R x := by
    rw [e.left_inv hx]
    apply real_pullbackField_inverse
    · exact (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    · exact (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    · filter_upwards [e.open_source.mem_nhds hx] with z hz using e.left_inv hz
  have hl : WeightedBound e.source τ m (JetPolynomial.tensorChartBudget m J D * C) R := by
    have hh := hp.congr (fun x hx => (hid x hx).symm)
    convert hh using 1
    unfold JetPolynomial.tensorChartBudget
    ring
  exact hl.extend_support e.open_source hRs
    (mul_nonneg (JetPolynomial.tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hC)

end ClosedSurfaceR4.PhaseMean

end

end OAI
