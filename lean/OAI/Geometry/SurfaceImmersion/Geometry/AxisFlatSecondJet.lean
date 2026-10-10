import OAI.Geometry.SurfaceImmersion.Whitney.RulingDirectionJet

namespace OAI

/-! Vanishing of the first jet on an axis also fixes every second
 derivative with one longitudinal argument. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma axis_flat_second_vertical {q : Base → V} (hq : ContDiff ℝ ∞ q)
    (hD : ∀ t, fderiv ℝ q (crosscapAxis t) = 0) (t : ℝ) (v : Base) :
    fderiv ℝ (fderiv ℝ q) (crosscapAxis t) v (![0,1] : Base) = 0 := by
  have hd := ((hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    (crosscapAxis t)).hasFDerivAt.comp_hasDerivAt t crosscapAxis.hasFDerivAt.hasDerivAt
  have he : (fderiv ℝ q) ∘ crosscapAxis = 0 := funext hD
  change HasDerivAt ((fderiv ℝ q) ∘ crosscapAxis) _ t at hd
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (0 : Base →L[ℝ] V))
  have hsym := (hq.contDiffAt (x := crosscapAxis t)).isSymmSndFDerivAt (by simp) v (![0,1] : Base)
  rw [hsym]
  have hz' : fderiv ℝ (fderiv ℝ q) (crosscapAxis t) (![0,1] : Base) = 0 := by
    simpa only [crosscapAxis_apply] using hz
  rw [hz']
  rfl

lemma axis_flat_add_first {f q : Base → V} (hf : ContDiff ℝ ∞ f)
    (hq : ContDiff ℝ ∞ q) (hD : ∀ t, fderiv ℝ q (crosscapAxis t) = 0) (t : ℝ) :
    fderiv ℝ (f+q) (crosscapAxis t) = fderiv ℝ f (crosscapAxis t) := by
  rw [fderiv_add (hf.differentiable (by simp) _) (hq.differentiable (by simp) _),hD,add_zero]

lemma axis_flat_add_direction {f q : Base → V} (hf : ContDiff ℝ ∞ f)
    (hq : ContDiff ℝ ∞ q) (hD : ∀ t, fderiv ℝ q (crosscapAxis t) = 0) (t : ℝ) :
    axisDirectionJet (f+q) (crosscapAxis t) = axisDirectionJet f (crosscapAxis t) := by
  have hfun : fderiv ℝ (f+q) = fderiv ℝ f+fderiv ℝ q := by
    funext x
    exact fderiv_add (hf.differentiable (by simp) x) (hq.differentiable (by simp) x)
  apply ContinuousLinearMap.ext
  intro z
  rw [axisDirectionJet_apply,axisDirectionJet_apply,axis_flat_add_first hf hq hD,hfun,
    fderiv_add ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _)
      ((hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _)]
  simp only [add_apply,axis_flat_second_vertical hq hD,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
