import Mathlib

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma hasFDerivAt_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    HasFDerivAt (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (tangentCoordChange 𝓘(ℝ,E) a b x) (extChartAt 𝓘(ℝ,E) a x) := by
  simpa only [ModelWithCorners.range_eq_univ,hasFDerivWithinAt_univ] using
    hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ,E)) ⟨ha,hb⟩

lemma contDiffAt_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (extChartAt 𝓘(ℝ,E) a x) := by
  have h1 := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt 𝓘(ℝ,E) a).map_source ha))
  have h2 := (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (n := ∞) (x := b)).contMDiffAt
    (by simpa only [extChartAt_source] using ((isOpen_extChartAt_source b).mem_nhds hb))
  have h2' : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) b)
      ((extChartAt 𝓘(ℝ,E) a).symm (extChartAt 𝓘(ℝ,E) a x)) := by
    rwa [(extChartAt 𝓘(ℝ,E) a).left_inv ha]
  exact (h2'.comp _ h1).contDiffAt

lemma chart_transition_derivative_surjective {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) :
    Function.Surjective (fderiv ℝ
      (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
      (extChartAt 𝓘(ℝ,E) a x)) := by
  rw [(hasFDerivAt_chart_transition ha hb).fderiv]
  intro v
  refine ⟨tangentCoordChange 𝓘(ℝ,E) b a x v,?_⟩
  rw [tangentCoordChange_comp ⟨⟨hb,ha⟩,hb⟩,tangentCoordChange_self hb]

lemma symmL_chart_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source) (v : E) :
    (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x
      (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
        (extChartAt 𝓘(ℝ,E) a x) v) =
    (trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x v := by
  have ha' : x ∈ (chartAt E a).source := by simpa only [extChartAt_source] using ha
  have hb' : x ∈ (chartAt E b).source := by simpa only [extChartAt_source] using hb
  rw [(hasFDerivAt_chart_transition ha hb).fderiv,
    Trivialization.symmL_apply _ hb', Trivialization.symmL_apply _ ha']
  have hsA (u : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) a).symm x u =
      tangentCoordChange 𝓘(ℝ,E) a x x u :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E a) ha' u
  have hsB (u : E) : (trivializationAt E (TangentSpace 𝓘(ℝ,E)) b).symm x u =
      tangentCoordChange 𝓘(ℝ,E) b x x u :=
    (tangentBundleCore 𝓘(ℝ,E) M).localTriv_symm_apply (i := achart E b) hb' u
  rw [hsA,hsB]
  have h := tangentCoordChange_comp (I := 𝓘(ℝ,E)) (w := a) (x := b) (y := x)
    (z := x) (v := v) ⟨⟨ha,hb⟩,mem_extChartAt_source x⟩
  exact h

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma chart_metric_transition {a b x : M}
    (ha : x ∈ (extChartAt 𝓘(ℝ,E) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℝ,E) b).source)
    {g h : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ u v : E, g (extChartAt 𝓘(ℝ,E) a x) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) a).symmL ℝ x v))
    (hh : ∀ u v : E, h (extChartAt 𝓘(ℝ,E) b x) u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) b).symmL ℝ x v))
    (u v : E) :
    g (extChartAt 𝓘(ℝ,E) a x) u v =
      h (extChartAt 𝓘(ℝ,E) b x)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
          (extChartAt 𝓘(ℝ,E) a x) u)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) b ∘ (extChartAt 𝓘(ℝ,E) a).symm)
          (extChartAt 𝓘(ℝ,E) a x) v) := by
  rw [hg,hh,symmL_chart_transition ha hb,symmL_chart_transition ha hb]

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma tangent_chart_apply (c z : TangentBundle 𝓘(ℝ,E) M) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c z =
      (extChartAt 𝓘(ℝ,E) c.1 z.1, tangentCoordChange 𝓘(ℝ,E) z.1 c.1 z.1 z.2) := by
  rfl

lemma tangent_chart_symm_base (c : TangentBundle 𝓘(ℝ,E) M) (z : E × E) :
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c).symm z).1 = (extChartAt 𝓘(ℝ,E) c.1).symm z.1 := by
  rfl

lemma tangent_chart_symm_fiber (c : TangentBundle 𝓘(ℝ,E) M) (z : E × E) :
    ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) c).symm z).2 =
      tangentCoordChange 𝓘(ℝ,E) c.1 ((extChartAt 𝓘(ℝ,E) c.1).symm z.1)
        ((extChartAt 𝓘(ℝ,E) c.1).symm z.1) z.2 := by
  rfl

lemma tangent_chart_transition_apply (a b : TangentBundle 𝓘(ℝ,E) M) (z : E × E)
    (ha : z.1 ∈ (extChartAt 𝓘(ℝ,E) a.1).target)
    (hb : (extChartAt 𝓘(ℝ,E) a.1).symm z.1 ∈ (extChartAt 𝓘(ℝ,E) b.1).source) :
    extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) b ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a).symm z) =
      ((extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) z.1,
        fderiv ℝ (extChartAt 𝓘(ℝ,E) b.1 ∘ (extChartAt 𝓘(ℝ,E) a.1).symm) z.1 z.2) := by
  rw [tangent_chart_apply,tangent_chart_symm_base,tangent_chart_symm_fiber]
  apply Prod.ext
  · rfl
  · have hsrc := (extChartAt 𝓘(ℝ,E) a.1).map_target ha
    rw [tangentCoordChange_comp ⟨⟨hsrc,mem_extChartAt_source _⟩,hb⟩]
    simp only [tangentCoordChange_def,ModelWithCorners.range_eq_univ,fderivWithin_univ,
      (extChartAt 𝓘(ℝ,E) a.1).right_inv ha]

end WeakMTWTransport

end

end OAI
