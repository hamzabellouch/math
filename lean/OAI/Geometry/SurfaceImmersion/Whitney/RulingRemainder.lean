import OAI.Geometry.SurfaceImmersion.Atlas.TransverseCutoff

namespace OAI

/-! A longitudinally supported ruled remainder is flat to first order
on the whole axis and stays supported over the selected longitudinal set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def rulingRemainder (f : Base → ProjectionTarget 3) (η : ℝ → ℝ) (x : Base) : ProjectionTarget 3 :=
  η (x 1) • (transverseRuling f x-f x)

lemma rulingRemainder_smooth {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) : ContDiff ℝ ∞ (rulingRemainder f η) :=
  (hη.comp (contDiff_apply ℝ ℝ (1 : Fin 2))).smul ((transverseRuling_smooth hf).sub hf)

lemma rulingRemainder_axis (f : Base → ProjectionTarget 3) (η : ℝ → ℝ) (t : ℝ) :
    rulingRemainder f η (crosscapAxis t) = 0 := by
  simp [rulingRemainder,transverseRuling_axis]

lemma rulingRemainder_first_jet {f : Base → ProjectionTarget 3} {η : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (t : ℝ) :
    fderiv ℝ (rulingRemainder f η) (crosscapAxis t) = 0 := by
  have hηD := ((hη.comp (contDiff_apply ℝ ℝ (1 : Fin 2))).differentiable (by simp)
    (crosscapAxis t)).hasFDerivAt
  have hRD := ((transverseRuling_smooth hf).differentiable (by simp) (crosscapAxis t)).hasFDerivAt.sub
    (hf.differentiable (by simp) (crosscapAxis t)).hasFDerivAt
  have hd := hηD.smul hRD
  change HasFDerivAt (rulingRemainder f η) _ (crosscapAxis t) at hd
  rw [hd.fderiv,transverseRuling_first_jet hf,sub_self]
  simp [Pi.sub_apply,transverseRuling_axis]

lemma rulingRemainder_support (f : Base → ProjectionTarget 3) (η : ℝ → ℝ) :
    tsupport (rulingRemainder f η) ⊆ {x | x 1 ∈ tsupport η} := by
  apply closure_minimal _ (isClosed_tsupport η |>.preimage (continuous_apply 1))
  intro x hx
  by_contra hn
  have hz : η (x 1) = 0 := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [rulingRemainder,hz])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
