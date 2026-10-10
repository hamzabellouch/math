import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedRicci.MatrixCompactBounds
import OAI.Geometry.PrescribedRicci.TraceEntryBounds
import OAI.Geometry.PrescribedPotential.VolumePath
import OAI.Geometry.PrescribedRicci.CurvatureCompactBounds
import OAI.Geometry.PrescribedRicci.KahlerVolumeVariation
import OAI.Geometry.PrescribedRicci.MongeAmpereL2
import OAI.Geometry.PrescribedRicci.TraceMaximum

namespace OAI

/-! Compact Path Bounds. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

theorem volumePath_metric_bounds_on_compact (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) (q : Fin A.count) {L : Set (Coordinates d)}
    (hL : IsCompact L) (hLt : L ⊆ (A.chart q).target) : ∃ K : ℝ, 0 < K ∧
    ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ), g.integral φ.value = 0 →
    ∀ (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
    (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
    ∀ z ∈ L, ‖(g.deform φ hp).matrix q z‖ ≤ K ∧
      ‖((g.deform φ hp).matrix q z)⁻¹‖ ≤ K := by
  have hd' : 0 < d := by omega
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd'
  obtain ⟨T,hT,htrace⟩ := g.volumePath_trace_bound line hd
  obtain ⟨m,hm⟩ := hL.bddAbove_image
    ((g.backgroundSize_continuousOn (prescribedForcing g line) q).mono hLt)
  let M := max 1 m
  have hM : 1 ≤ M := le_max_left _ _
  have hbg (z : Coordinates d) (hz : z ∈ L) :
      g.BackgroundComponentBound (prescribedForcing g line) q z M :=
    g.backgroundComponents_of_size _ q z ((hm (mem_image_of_mem _ hz)).trans (le_max_right _ _))
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨D,hD,hdet⟩ := MongeAmpere.compact_matrix_bound
    (show Continuous (fun H : Matrix (Fin d) (Fin d) ℂ => H.det.re) from
      Complex.continuous_re.comp continuous_id.matrix_det) M
  obtain ⟨Q,hQ,hmetric⟩ := MongeAmpere.metric_norm_bound_from_inverse (n:=Fin d) (M*T)
  let E := Real.exp (2*‖(⟨(prescribedForcing g line).value,
    (prescribedForcing g line).continuous⟩ : C(X,ℝ))‖)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨1+M*T+E*D*Q,by positivity,?_⟩
  intro φ hp hmean t b ht heq z hzL
  have hz := hLt hzL
  let x := (A.chart q).symm z
  have hxs := (A.chart q).map_target hz
  have hxz : A.chart q x = z := (A.chart q).right_inv hz
  let H := (g.deform φ hp).matrix q z
  have hH := (g.deform φ hp).positive q z hz
  have hbi : ‖H⁻¹‖ ≤ M*T := by
    apply MongeAmpere.matrix_norm_le_of_entries (mul_nonneg hM0 hT.le)
    intro i j
    have hi := MongeAmpere.entry_le_relative_trace H⁻¹ (g.matrix q z) hH.inv
      (g.positive q _ hz) hM0
      (fun i => (Complex.re_le_norm _).trans ((hbg z hzL).2.1 i i)) i j
    have hs := htrace φ hp hmean t b ht heq x
    change (g.deform φ hp).traceMetricValue g x ≤ T at hs
    rw [(g.deform φ hp).traceMetricValue_local g q hxs,hxz] at hs
    exact hi.trans (mul_le_mul_of_nonneg_left hs hM0)
  have hdh : H.det.re ≤ E*D := by
    have hv := g.density_mul_volume φ q hz
    change (g.potentialDensity φ).value x*(g.matrix q z).det.re = H.det.re at hv
    rw [← hv]
    have hρ := (g.volumePath_density_bounds line ht hp heq x).2
    change (g.potentialDensity φ).value x ≤ E at hρ
    exact mul_le_mul hρ
      (hdet _ (MongeAmpere.matrix_norm_le_of_entries hM0 (hbg z hzL).1))
      (Complex.pos_iff.mp (g.positive q _ hz).det_pos).1.le hE.le
  constructor
  · have hb := (hmetric H hH hbi).trans (mul_le_mul_of_nonneg_right hdh hQ.le)
    change ‖H‖ ≤ _
    nlinarith [mul_nonneg hM0 hT.le]
  · change ‖H⁻¹‖ ≤ _
    nlinarith [mul_nonneg (mul_nonneg hE.le hD.le) hQ.le]

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
