import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PositiveTestMass
import OAI.Geometry.TamingCompatibility.Concentration.RadialDefect

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory RadialPotential
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)

def unitChartDomain (p : X) (K : Set Space) : Set (MetricUnit (hermitianMetric J α hs ht)) :=
  {u | u.val.proj ∈ (extChartAt Model p).symm '' K}

def unitChartBase (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  extChartAt Model p u.val.proj

def unitChartVector (p : X) (u : MetricUnit (hermitianMetric J α hs ht)) : Space :=
  ((trivializationAt Space (TangentSpace Model) p) u.val).2

omit [CompactSpace X] in
lemma unitChartDomain_closed (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    _root_.IsClosed (unitChartDomain J α hs ht p K) :=
  (inverse_chart_compact_image p hK hKT).isClosed.preimage
    ((FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val)

omit [CompactSpace X] [T2Space X] in
lemma unitChart_mem (p : X) {K : Set Space} (hKT : K ⊆ (extChartAt Model p).target)
    {u : MetricUnit (hermitianMetric J α hs ht)} (hu : u ∈ unitChartDomain J α hs ht p K) :
    u.val.proj ∈ (extChartAt Model p).source ∧ unitChartBase J α hs ht p u ∈ K := by
  obtain ⟨z,hz,he⟩ := hu
  refine ⟨he ▸ (extChartAt Model p).map_target (hKT hz),?_⟩
  change extChartAt Model p u.val.proj ∈ K
  rw [← he,(extChartAt Model p).right_inv (hKT hz)]
  exact hz

omit [CompactSpace X] [T2Space X] in
lemma unitChartBase_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartBase J α hs ht p) (unitChartDomain J α hs ht p K) := by
  apply (continuousOn_extChartAt p).comp
    (((FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp
      continuous_subtype_val).continuousOn)
  exact fun u hu => (unitChart_mem J α hs ht p hKT hu).1

omit [CompactSpace X] [T2Space X] in
lemma unitChartVector_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartVector J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  have hb : u.val.proj ∈ (trivializationAt Space (TangentSpace Model) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using
      (unitChart_mem J α hs ht p hKT hu).1
  exact (((trivializationAt Space (TangentSpace Model) p).continuousAt
    ((trivializationAt Space (TangentSpace Model) p).mem_source.mpr hb)).comp
      continuous_subtype_val.continuousAt).snd.continuousWithinAt

omit [CompactSpace X] [T2Space X] in
lemma unitChart_eval (p : X) (β : TwoForm X) (hβ : IsSmooth β)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
      ![unitChartVector J α hs ht p u,
        coordinateJ J p (unitChartBase J α hs ht p u) (unitChartVector J α hs ht p u)] =
      unitEvaluation J (hermitianMetric J α hs ht) β hβ u := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  dsimp only [unitChartBase]
  rw [pullback_complexLine J β p ((extChartAt Model p).map_source hu),
    inverseChart_derivative p ((extChartAt Model p).map_source hu)]
  change eval β ((extChartAt Model p).symm (extChartAt Model p u.val.proj))
    (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)
    (J.endomorphism _ (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)) = _
  rw [(extChartAt Model p).left_inv hu,hv]
  rfl

def unitRadialDefect (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  hermitianDefect (coordinateJ J p b) (unitChartBase J α hs ht p u-b)
    (unitChartVector J α hs ht p u)

def unitRadialRadius (p : X) (b : Space) (u : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  ‖hermitianGraph (coordinateJ J p b) (unitChartBase J α hs ht p u-b)‖

omit [CompactSpace X] [T2Space X] in
lemma unitRadialDefect_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitRadialDefect J α hs ht p b) (unitChartDomain J α hs ht p K) := by
  let G := hermitianGraph (coordinateJ J p b)
  have hz := G.continuous.comp_continuousOn ((unitChartBase_continuousOn J α hs ht p hKT).sub (continuousOn_const (c := b)))
  have hv := G.continuous.comp_continuousOn (unitChartVector_continuousOn J α hs ht p hKT)
  have hjv := G.continuous.comp_continuousOn ((coordinateJ J p b).continuous.comp_continuousOn
    (unitChartVector_continuousOn J α hs ht p hKT))
  exact ((hz.norm.pow 2).mul (hv.norm.pow 2) |>.sub ((hz.inner hv).pow 2)).sub ((hz.inner hjv).pow 2)

omit [CompactSpace X] [T2Space X] in
lemma unitRadialRadius_continuousOn (p : X) (b : Space) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitRadialRadius J α hs ht p b) (unitChartDomain J α hs ht p K) :=
  ((hermitianGraph (coordinateJ J p b)).continuous.comp_continuousOn
    ((unitChartBase_continuousOn J α hs ht p hKT).sub (continuousOn_const (c := b)))).norm

omit [CompactSpace X] [T2Space X] in
lemma unitRadialDefect_nonneg (p : X) {b : Space} (hb : b ∈ (extChartAt Model p).target)
    (u : MetricUnit (hermitianMetric J α hs ht)) : 0 ≤ unitRadialDefect J α hs ht p b u :=
  hermitianDefect_nonneg _ (coordinateJ_square J p hb) _ _

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
