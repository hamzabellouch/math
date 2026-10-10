import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GeometricQuadraticMass
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShell

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

omit [MeasurableSpace X] [BorelSpace X] in
lemma hermitianEDist_continuous (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) :
    Continuous (fun p : X×X => hermitianEDist J α hs ht p.1 p.2) := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let : EMetricSpace X := .ofRiemannianMetric Model X
  exact continuous_fst.edist continuous_snd

omit [MeasurableSpace X] [BorelSpace X] in
lemma hermitianEDist_unit_measurable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x : X) :
    Measurable (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      hermitianEDist J α hs ht x u.val.proj) := by
  have hp := (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp
    (continuous_subtype_val : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val))
  exact ((hermitianEDist_continuous J α hs ht).comp (continuous_const.prodMk hp)).measurable

theorem separating_probability_shell
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      ∫⁻ u, QuadraticShell.profile r (hermitianEDist J α hs ht x u.val.proj) ∂μ ≤
        ENNReal.ofReal (C*r^2) := by
  obtain ⟨C,hC,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  refine ⟨8*C,by positivity,fun x r hr => ?_⟩
  exact QuadraticShell.lintegral_profile_le μ _ (hermitianEDist_unit_measurable J α hs ht x)
    C hC (hgrowth x) hr

end TamingCompatibility

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms Set MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma hermitianEDist_ne_top (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) :
    hermitianEDist J α hs ht x y ≠ ⊤ := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  let : EMetricSpace X := .ofRiemannianMetric Model X
  change edist x y ≠ ⊤
  have hb : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from
      ⟨Metric.isClosed_eball_top,Metric.isOpen_eball⟩).eq_univ
      ⟨x,by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hb]; trivial
  exact (by simpa only [Metric.mem_eball,edist_comm] using hy : edist x y < ⊤).ne

lemma hermitian_profile_toReal (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) {r : ℝ} (hr : 0 < r) :
    (QuadraticShell.profile r (hermitianEDist J α hs ht x y)).toReal =
      (1+(hermitianEDist J α hs ht x y).toReal/r)⁻¹^6 := by
  have hd := hermitianEDist_ne_top J α hs ht x y
  conv_lhs => rw [← ENNReal.ofReal_toReal hd, QuadraticShell.profile_ofReal hr ENNReal.toReal_nonneg]
  rw [ENNReal.toReal_ofReal (by positivity)]

end TamingCompatibility

end
end

end
end

end OAI
