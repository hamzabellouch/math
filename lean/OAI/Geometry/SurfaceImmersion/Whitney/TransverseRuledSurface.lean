import OAI.Geometry.SurfaceImmersion.Geometry.AxisDirectionJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace OAI

/-! The ruled map retaining the original value and transverse first jet
along the full joining axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def axisValue (f : Base → V) (t : ℝ) : V := f (crosscapAxis t)
def axisTransverse (f : Base → V) (t : ℝ) : V :=
  fderiv ℝ f (crosscapAxis t) (![1,0] : Base)
def transverseRuling (f : Base → V) (x : Base) : V :=
  axisValue f (x 1) + (x 0) • axisTransverse f (x 1)

lemma axisValue_smooth {f : Base → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (axisValue f) := hf.comp crosscapAxis.contDiff
lemma axisTransverse_smooth {f : Base → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (axisTransverse f) :=
  ((hf.fderiv_right (m := ∞) (by simp)).comp crosscapAxis.contDiff).clm_apply contDiff_const
lemma transverseRuling_smooth {f : Base → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (transverseRuling f) := by
  exact ((axisValue_smooth hf).comp (contDiff_apply ℝ ℝ (1 : Fin 2))).add
    ((contDiff_apply ℝ ℝ (0 : Fin 2)).smul ((axisTransverse_smooth hf).comp (contDiff_apply ℝ ℝ (1 : Fin 2))))

lemma transverseRuling_axis (f : Base → V) (t : ℝ) :
    transverseRuling f (crosscapAxis t) = f (crosscapAxis t) := by
  simp [transverseRuling,axisValue,crosscapAxis_apply]

lemma axisValue_deriv {f : Base → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (axisValue f) t = fderiv ℝ f (crosscapAxis t) (![0,1] : Base) := by
  exact ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt).deriv.trans (by simp only [crosscapAxis_apply])

lemma axisTransverse_deriv {f : Base → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (axisTransverse f) t =
      fderiv ℝ (fderiv ℝ f) (crosscapAxis t) (![0,1] : Base) (![1,0] : Base) := by
  have hd := (((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t crosscapAxis.hasFDerivAt.hasDerivAt).clm_apply (hasDerivAt_const t (![1,0] : Base))
  change HasDerivAt (axisTransverse f) _ t at hd
  rw [hd.deriv]
  simp [crosscapAxis_apply]

lemma transverseRuling_fderiv {f : Base → V} (hf : ContDiff ℝ ∞ f) (x v : Base) :
    fderiv ℝ (transverseRuling f) x v =
      (v 1) • deriv (axisValue f) (x 1) +
        (v 0) • axisTransverse f (x 1) +
        (x 0) • ((v 1) • deriv (axisTransverse f) (x 1)) := by
  have hv := ((axisValue_smooth hf).differentiable (by simp) _).hasDerivAt.hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x)
  have ht := ((axisTransverse_smooth hf).differentiable (by simp) _).hasDerivAt.hasFDerivAt.comp x (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x)
  have hd := hv.add ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x).smul ht)
  change HasFDerivAt (transverseRuling f) _ x at hd
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
    add_assoc,add_comm]


lemma transverseRuling_first_jet {f : Base → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    fderiv ℝ (transverseRuling f) (crosscapAxis t) = fderiv ℝ f (crosscapAxis t) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [transverseRuling_fderiv hf,axisValue_deriv hf]
  have hv : v = (v 0) • (![1,0] : Base) + (v 1) • (![0,1] : Base) := by
    ext i; fin_cases i <;> simp
  simp only [crosscapAxis_apply,Matrix.cons_val_zero,zero_smul,add_zero]
  conv_rhs => rw [hv,map_add,map_smul,map_smul]
  simpa [axisTransverse,crosscapAxis_apply] using (add_comm ((v 1) • fderiv ℝ f (![0,t]) (![0,1] : Base)) ((v 0) • fderiv ℝ f (![0,t]) (![1,0] : Base)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
