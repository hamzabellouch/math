import Mathlib
import OAI.Geometry.PrescribedRicci.ChernLuAlgebra
import OAI.Geometry.PrescribedRicci.CurvatureCompactBounds
import OAI.Geometry.PrescribedRicci.VolumePathRicci
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Compact Path Ricci. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma volumePath_holDerivative_congr {f h : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (he : f =ᶠ[nhds z] h) (a : Fin d) :
    holDerivative f z a = holDerivative h z a := by unfold holDerivative; rw [he.fderiv_eq]

lemma holDerivative_sub_smul {f h : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (t : ℂ) (a : Fin d) :
    holDerivative (fun y => f y-t • h y) z a = holDerivative f z a-t • holDerivative h z a := by
  unfold holDerivative
  have he : fderiv ℝ (fun y => f y-t • h y) z = fderiv ℝ f z-t • fderiv ℝ h z := by
    convert! (hf.hasFDerivAt.sub (hh.hasFDerivAt.const_smul t)).fderiv using 1
  rw [he]
  simp only [_root_.sub_apply,_root_.smul_apply,smul_sub,
    smul_smul]
  module

lemma volumePath_ricci_hol (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (hp : g.PositivePotential φ)
    (heq : ∀ x, (g.logRatio (g.deform φ hp)).value x =
      t*(prescribedForcing g line).value x+b)
    (q : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holDerivative ((g.deform φ hp).curvatureRicci q) z a =
      holDerivative (g.curvatureRicci q) z a-
        (t:ℂ) • holDerivative ((prescribedForcing g line).hessian q) z a := by
  have he := Filter.eventually_of_mem ((A.chart q).open_target.mem_nhds hz)
    (fun y hy => g.volumePath_ricci line hp heq q hy)
  rw [volumePath_holDerivative_congr he,holDerivative_sub_smul
    ((g.curvatureRicci_smooth q hz).differentiableAt (by simp))
    ((((prescribedForcing g line).hessian_smooth q).contDiffAt
      ((A.chart q).open_target.mem_nhds hz)).differentiableAt (by simp))]

lemma volumePath_ricci_bounds_on_compact (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (q : Fin A.count) {L : Set (Coordinates d)}
    (hL : IsCompact L) (hLt : L ⊆ (A.chart q).target) :
    ∃ R : ℝ, 0 < R ∧ ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
      (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
      (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
      ∀ z ∈ L, ‖(g.deform φ hp).curvatureRicci q z‖ ≤ R ∧
        ∀ a, ‖holDerivative ((g.deform φ hp).curvatureRicci q) z a‖ ≤ R := by
  let F := prescribedForcing g line
  let size : Coordinates d → ℝ := fun z => ‖g.curvatureRicci q z‖+‖F.hessian q z‖+
    ‖holDerivative (g.curvatureRicci q) z‖+‖holDerivative (F.hessian q) z‖
  have hs : ContinuousOn size L := by
    intro z hz
    have hR := g.curvatureRicci_smooth q (hLt hz)
    have hF := (F.hessian_smooth q).contDiffAt ((A.chart q).open_target.mem_nhds (hLt hz))
    have hdR : ContDiffAt ℝ ∞ (fun y => holDerivative (g.curvatureRicci q) y) z :=
      contDiffAt_pi.mpr (fun a => contDiffAt_holDerivative hR a)
    have hdF : ContDiffAt ℝ ∞ (fun y => holDerivative (F.hessian q) y) z :=
      contDiffAt_pi.mpr (fun a => contDiffAt_holDerivative hF a)
    exact (((hR.continuousAt.norm.add hF.continuousAt.norm).add hdR.continuousAt.norm).add
      hdF.continuousAt.norm).continuousWithinAt
  obtain ⟨r,hr⟩ := hL.bddAbove_image hs
  refine ⟨1+max 0 r,by positivity,?_⟩
  intro φ hp t b ht heq z hz
  have htr : ‖(t:ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2
  have hb : size z ≤ 1+max 0 r := (hr (mem_image_of_mem _ hz)).trans (by linarith [le_max_right (0:ℝ) r])
  constructor
  · rw [g.volumePath_ricci line hp heq q (hLt hz)]
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    have hn := mul_le_mul_of_nonneg_right htr (norm_nonneg (F.hessian q z))
    change ‖g.curvatureRicci q z‖+‖(t:ℂ)‖*‖F.hessian q z‖ ≤ _
    dsimp [size] at hb
    linarith [norm_nonneg (holDerivative (g.curvatureRicci q) z),norm_nonneg (holDerivative (F.hessian q) z)]
  · intro a
    rw [g.volumePath_ricci_hol line hp heq q (hLt hz) a]
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    have hn := mul_le_mul_of_nonneg_right htr (norm_nonneg (holDerivative (F.hessian q) z a))
    have h1 := norm_le_pi_norm (holDerivative (g.curvatureRicci q) z) a
    have h2 := norm_le_pi_norm (holDerivative (F.hessian q) z) a
    change ‖holDerivative (g.curvatureRicci q) z a‖+‖(t:ℂ)‖*‖holDerivative (F.hessian q) z a‖ ≤ _
    dsimp [size] at hb
    linarith [norm_nonneg (g.curvatureRicci q z),norm_nonneg (F.hessian q z)]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
