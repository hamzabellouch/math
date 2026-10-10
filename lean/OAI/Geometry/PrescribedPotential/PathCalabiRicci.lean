import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiCovariant
import OAI.Geometry.PrescribedPotential.CalabiTensorAlgebra
import OAI.Geometry.PrescribedPotential.MatrixTensorCalculus
import OAI.Geometry.PrescribedPotential.PathRicci

namespace OAI

/-! Path Calabi Ricci. -/

section

noncomputable section
open Set Filter Topology Matrix Metric
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace KaehlerMetric

def localField (g : KaehlerMetric A) (i : Fin A.count) : LocalKaehlerField d where
  domain := (A.chart i).target
  isOpen := (A.chart i).open_target
  matrix := g.matrix i
  smooth := g.smooth i
  positive := g.positive i
  closed := g.closed i

end KaehlerMetric

def pathRicciJet (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) (t : ℝ) (z : Coordinates d) : ConnectionTensor d := fun k =>
  ((1-t:ℝ):ℂ) • mderiv (-Complex.I) (e k)
      (PotentialKaehler.potentialMatrix (fun y => Real.log (g.matrix i y).det.re)) z -
    (t:ℂ) • mderiv (-Complex.I) (e k) (PotentialKaehler.potentialMatrix (h.weight i)) z

lemma pathLogDetHessian_jet (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) (t : ℝ) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (fun k => mderiv (-Complex.I) (e k) (pathLogDetHessian g h i t) z) = pathRicciJet g h i t z := by
  have hf := (g.localField i).ricciHessian_smooth.contDiffAt ((A.chart i).open_target.mem_nhds hz)
  change ContDiffAt ℝ ∞ (PotentialKaehler.potentialMatrix (fun y => Real.log (g.matrix i y).det.re)) z at hf
  have hh := PotentialKaehler.potentialMatrix_smooth ((h.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz))
  funext k
  unfold pathLogDetHessian pathRicciJet
  rw [mderiv_sub (matrix_smooth_smul (contDiffAt_const (c := ((1-t:ℝ):ℂ))) hf) (matrix_smooth_smul (contDiffAt_const (c := (t:ℂ))) hh),
    mderiv_smul contDiffAt_const hf,mderiv_smul contDiffAt_const hh]
  simp only [wderiv_const,zero_smul,zero_add]

lemma volumePath_ricciJet (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hs : SolvesVolumePath g h t φ b)
    (hp : g.PositivePotential φ) (i : Fin A.count) {z : Coordinates d}
    (hz : z ∈ (A.chart i).target) :
    (fun k => mderiv (-Complex.I) (e k) ((g.deform φ hp).localField i).ricciHessian z) =
      pathRicciJet g h i t z := by
  have he : ((g.deform φ hp).localField i).ricciHessian =ᶠ[𝓝 z] pathLogDetHessian g h i t := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact volumePath_logdet_hessian g h hs hp i hy
  rw [← pathLogDetHessian_jet g h i t hz]
  funext k
  exact mderiv_congr he _ _

lemma pathRicciJet_continuous (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) : ContinuousOn (fun q : ℝ × Coordinates d => pathRicciJet g h i q.1 q.2)
      (univ ×ˢ (A.chart i).target) := by
  apply continuousOn_pi.mpr
  intro k
  have hf : ContinuousOn (mderiv (-Complex.I) (e k) (g.localField i).ricciHessian) (A.chart i).target := by
    intro z hz
    exact (mderiv_smooth ((g.localField i).ricciHessian_smooth.contDiffAt
      ((A.chart i).open_target.mem_nhds hz)) _ _).continuousAt.continuousWithinAt
  have hh : ContinuousOn (mderiv (-Complex.I) (e k) (PotentialKaehler.potentialMatrix (h.weight i))) (A.chart i).target := by
    intro z hz
    exact (mderiv_smooth (PotentialKaehler.potentialMatrix_smooth ((h.smooth i).contDiffAt
      ((A.chart i).open_target.mem_nhds hz))) _ _).continuousAt.continuousWithinAt
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).continuousOn.smul
    (hf.comp continuous_snd.continuousOn (fun _ h => h.2))).sub
    ((Complex.continuous_ofReal.comp continuous_fst).continuousOn.smul
      (hh.comp continuous_snd.continuousOn (fun _ h => h.2)))
end Anticanonical.SourceSmooth

end
end

end OAI
