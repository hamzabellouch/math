import Mathlib
import OAI.Geometry.PrescribedPotential.PathMetricBootstrap
import OAI.Geometry.PrescribedPotential.UniformCompositionFamily

namespace OAI

/-! Path Laplace Jets. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel MetricSystem HigherJet GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  {A : ComplexAtlas d X}
local instance pathLapECIP : InnerProductSpace ℝ (EC d) := InnerProductSpace.rclikeToReal ℂ (EC d)
local instance pathLapHMIP : InnerProductSpace ℝ (HM d) := InnerProductSpace.rclikeToReal ℂ (HM d)

lemma path_metric_all_jets (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) {K : Set (EC d)} (hK : IsCompact K)
    (hKU : K ⊆ (A.euclideanChart i).target) (m : ℕ) :
    ∃ C : ℝ, ∀ (s : PathSolution g h) x, x ∈ K →
      ‖iteratedFDeriv ℝ m (fun y => encode d (s.metric.matrix i (coordinateEquiv d y))) x‖ ≤ C := by
  by_cases hm : 1 ≤ m
  · obtain ⟨C,hC,hb⟩ := path_metric_higher_bounds g h i m hm K hK hKU
    exact ⟨C,hb⟩
  · have hm0 : m=0 := by omega
    subst m
    obtain ⟨C,hC,hb⟩ := path_metric_compact_C1 g h i hK hKU
    refine ⟨‖encodeCLM d‖*C,fun s x hx => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    exact ((encodeCLM d).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb s x hx).1 (norm_nonneg _))

def laplaceMetricCoefficient (g : KaehlerMetric A) (i : Fin A.count)
    (p : EC d × HM d) : ℂ :=
  (((g.matrix i (coordinateEquiv d p.1))⁻¹ * ((encode d).symm p.2-g.matrix i (coordinateEquiv d p.1))).trace.re : ℂ)

omit [CompactSpace X] [ConnectedSpace X] in
lemma laplaceMetricCoefficient_smooth (g : KaehlerMetric A) (i : Fin A.count)
    {x : EC d} (hx : x ∈ (A.euclideanChart i).target) (u : HM d) :
    ContDiffAt ℝ ∞ (laplaceMetricCoefficient g i) (x,u) := by
  have hx' : coordinateEquiv d x ∈ (A.chart i).target := by
    simpa only [ComplexAtlas.euclideanChart_target,Set.mem_preimage] using hx
  have hG : ContDiffAt ℝ ∞ (fun p : EC d × HM d => g.matrix i (coordinateEquiv d p.1)) (x,u) :=
    ((g.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hx')).comp (x,u)
      ((coordinateEquiv d).contDiff.contDiffAt.comp (x,u) contDiffAt_fst)
  have hI := (MatrixSmoothGeneral.inverse (g.smooth i)
    (fun z hz => ne_of_gt (g.positive i z hz).det_pos)).contDiffAt ((A.chart i).open_target.mem_nhds hx')
  have hInv := hI.comp (x,u) ((coordinateEquiv d).contDiff.contDiffAt.comp (x,u) contDiffAt_fst)
  have hM : ContDiffAt ℝ ∞ (fun p : EC d × HM d => (encode d).symm p.2) (x,u) :=
    (encode d).symm.contDiff.contDiffAt.comp (x,u) contDiffAt_snd
  change ContDiffAt ℝ ∞ (fun p : EC d × HM d =>
    (((∑ k, ∑ l, (g.matrix i (coordinateEquiv d p.1))⁻¹ k l *
      ((encode d).symm p.2-g.matrix i (coordinateEquiv d p.1)) l k).re) : ℂ)) (x,u)
  apply Complex.ofRealCLM.contDiff.contDiffAt.comp (x,u)
  apply Complex.reCLM.contDiff.contDiffAt.comp (x,u)
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.sum
  intro l _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hInv k) l).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp (hM.sub hG) l) k)

omit [CompactSpace X] [ConnectedSpace X] in
lemma path_laplacian_local (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (s : PathSolution g h) (i : Fin A.count) {x : EC d} (hx : x ∈ (A.euclideanChart i).target) :
    Smooth.ofReal (g.laplacian s.potential) ((A.euclideanChart i).symm x) =
      laplaceMetricCoefficient g i (x,encode d (s.metric.matrix i (coordinateEquiv d x))) := by
  have hx' : coordinateEquiv d x ∈ (A.chart i).target := by
    simpa only [ComplexAtlas.euclideanChart_target,Set.mem_preimage] using hx
  change ((g.laplacian s.potential).localExpression i (coordinateEquiv d x) : ℂ) = _
  rw [g.laplacian_localExpression s.potential i hx']
  simp only [laplaceMetricCoefficient,ContinuousLinearEquiv.symm_apply_apply,PathSolution.metric,KaehlerMetric.deform,
    add_sub_cancel_left,KaehlerMetric.linearizedMongeAmpere]

lemma path_laplacian_weighted_jets (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) (ρ : Smooth A) {K : Set (EC d)} (hK : IsCompact K)
    (hKU : K ⊆ (A.euclideanChart i).target) (m : ℕ) :
    ∃ C : ℝ, ∀ (s : PathSolution g h) x, x ∈ K →
      ‖iteratedFDeriv ℝ m (fun y => ρ ((A.euclideanChart i).symm y)*
        Smooth.ofReal (g.laplacian s.potential) ((A.euclideanChart i).symm y)) x‖ ≤ C := by
  let u : PathSolution g h → EC d → HM d := fun s x => encode d (s.metric.matrix i (coordinateEquiv d x))
  let a : EC d × HM d → ℂ := fun p => ρ ((A.euclideanChart i).symm p.1)*laplaceMetricCoefficient g i p
  have hu (s : PathSolution g h) (x : EC d) (hx : x ∈ K) : ContDiffAt ℝ ∞ (u s) x := by
    have hx' : coordinateEquiv d x ∈ (A.chart i).target := by
      simpa only [ComplexAtlas.euclideanChart_target,Set.mem_preimage] using hKU hx
    exact (encode d).contDiff.contDiffAt.comp x
      (((s.metric.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hx')).comp x (coordinateEquiv d).contDiff.contDiffAt)
  have ha (x : EC d) (hx : x ∈ K) (v : HM d) : ContDiffAt ℝ ∞ a (x,v) := by
    have hw : ContDiffAt ℝ ∞ (fun y => ρ ((A.euclideanChart i).symm y)) x :=
      (ρ.smooth i).contDiffAt ((A.euclideanChart i).open_target.mem_nhds (hKU hx))
    exact (hw.comp (x,v) contDiffAt_fst).mul (laplaceMetricCoefficient_smooth g i (hKU hx) v)
  obtain ⟨C,hC⟩ := parametric_composition_family_jets u hK hu (path_metric_all_jets g h i hK hKU) a ha m
  refine ⟨C,fun s x hx => ?_⟩
  have he : (fun y => ρ ((A.euclideanChart i).symm y)*Smooth.ofReal (g.laplacian s.potential) ((A.euclideanChart i).symm y))
      =ᶠ[𝓝 x] (fun y => a (y,u s y)) := by
    filter_upwards [(A.euclideanChart i).open_target.mem_nhds (hKU hx)] with y hy
    exact congrArg (ρ ((A.euclideanChart i).symm y)*·) (path_laplacian_local g h s i hy)
  rw [(he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hC s x hx
end Anticanonical.SourceSmooth

end
end

end OAI
