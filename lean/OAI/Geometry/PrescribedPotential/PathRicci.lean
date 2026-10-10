import Mathlib
import OAI.Geometry.PrescribedPotential.PotentialLinearCalculus
import OAI.Geometry.PrescribedPotential.ScalarFrameCalculus
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Path Ricci. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

def pathLogDetHessian (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) (t : ℝ) (z : Coordinates d) : Matrix (Fin d) (Fin d) ℂ :=
  ((1-t:ℝ):ℂ) • PotentialKaehler.potentialMatrix (fun y => Real.log (g.matrix i y).det.re) z -
    (t:ℂ) • PotentialKaehler.potentialMatrix (h.weight i) z

lemma volumePath_logdet_local (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hs : SolvesVolumePath g h t φ b)
    (hp : g.PositivePotential φ) (i : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) :
    Real.log ((g.deform φ hp).matrix i z).det.re =
      (1-t)*Real.log (g.matrix i z).det.re-t*h.weight i z+b := by
  have he := hs.choose_spec ((A.chart i).symm z)
  change (g.logRatio (g.deform φ hs.choose)).localExpression i z =
    t*(prescribedForcing g h).localExpression i z+b at he
  rw [KaehlerMetric.logRatio_local _ _ i hz,prescribedForcing_local _ _ i hz] at he
  change Real.log ((g.deform φ hp).matrix i z).det.re - Real.log (g.matrix i z).det.re =
    t*(-h.weight i z-Real.log (g.matrix i z).det.re)+b at he
  linarith

lemma potentialMatrix_mul_const {f : KaehlerCalculus.V d → ℝ} {z : KaehlerCalculus.V d}
    (hf : ContDiffAt ℝ ∞ f z) (a : ℝ) :
    PotentialKaehler.potentialMatrix (fun y => a*f y) z =
      (a:ℂ) • PotentialKaehler.potentialMatrix f z := by
  have hh := potentialMatrix_affine (f := fun _ => 0) contDiffAt_const hf a
  have hz0 : PotentialKaehler.potentialMatrix (fun _ : KaehlerCalculus.V d => (0:ℝ)) z = 0 := by
    unfold PotentialKaehler.potentialMatrix
    ext i j
    simp [PotentialKaehler.hermitianPartMatrix, PotentialKaehler.hermitianPartForm, PotentialKaehler.hermitianPart]
    rfl
  simpa only [zero_add,hz0] using hh

lemma potentialMatrix_add_const (c : ℝ) (f : KaehlerCalculus.V d → ℝ) (z : KaehlerCalculus.V d) :
    PotentialKaehler.potentialMatrix (fun y => f y+c) z = PotentialKaehler.potentialMatrix f z := by
  simpa only [add_comm] using potentialMatrix_const_add c f z

lemma volumePath_logdet_hessian (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hs : SolvesVolumePath g h t φ b)
    (hp : g.PositivePotential φ) (i : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) :
    PotentialKaehler.potentialMatrix (fun y => Real.log ((g.deform φ hp).matrix i y).det.re) z =
      pathLogDetHessian g h i t z := by
  have he : (fun y => Real.log ((g.deform φ hp).matrix i y).det.re) =ᶠ[𝓝 z]
      (fun y => (1-t)*Real.log (g.matrix i y).det.re-t*h.weight i y+b) := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact volumePath_logdet_local g h hs hp i hy
  have hf : ContDiffAt ℝ ∞ (fun y => Real.log (g.matrix i y).det.re) z :=
    ((g.volumeCoefficient_smooth i).log (fun y hy => ne_of_gt (g.volumeCoefficient_pos i hy))).contDiffAt
      ((A.chart i).open_target.mem_nhds hz)
  have hh := (h.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)
  rw [PotentialKaehler.potentialMatrix_congr he,potentialMatrix_add_const,
    potentialMatrix_sub_smul (contDiffAt_const.mul hf) hh,potentialMatrix_mul_const hf]
  rfl

lemma pathLogDetHessian_continuous (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) :
    ContinuousOn (fun q : ℝ × Coordinates d => pathLogDetHessian g h i q.1 q.2)
      (univ ×ˢ (A.chart i).target) := by
  have hf : ContinuousOn (PotentialKaehler.potentialMatrix (fun y => Real.log (g.matrix i y).det.re))
      (A.chart i).target := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    apply ContDiffAt.continuousAt (𝕜 := ℝ) (n := ∞)
    apply PotentialKaehler.potentialMatrix_smooth
    exact ((g.volumeCoefficient_smooth i).log (fun y hy => ne_of_gt (g.volumeCoefficient_pos i hy))).contDiffAt
      ((A.chart i).open_target.mem_nhds hz)
  have hh : ContinuousOn (PotentialKaehler.potentialMatrix (h.weight i)) (A.chart i).target := by
    intro z hz
    exact (PotentialKaehler.potentialMatrix_smooth ((h.smooth i).contDiffAt
      ((A.chart i).open_target.mem_nhds hz))).continuousAt.continuousWithinAt
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).continuousOn.smul
    (hf.comp continuous_snd.continuousOn (fun _ h => h.2))).sub
    ((Complex.continuous_ofReal.comp continuous_fst).continuousOn.smul
      (hh.comp continuous_snd.continuousOn (fun _ h => h.2)))
end Anticanonical.SourceSmooth

end
end

end OAI
