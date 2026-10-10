import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayDistanceBound

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]

lemma tangent_chart_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) ⟨x,p⟩=
      (extChartAt 𝓘(ℝ,Model n) a x,
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p) := by
  rw [tangent_chart_apply,TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (by simpa only [extChartAt_source] using hx)]
  rfl

lemma tangent_chart_symm_trivialization {a : M} {q : Model n×Model n}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).symm q=
      (⟨(extChartAt 𝓘(ℝ,Model n) a).symm q.1,
        (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
  have hx : (extChartAt 𝓘(ℝ,Model n) a).symm q.1∈(chartAt (Model n) a).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,Model n) a).map_target hq
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

variable [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def minimizingChartParameters (a : M) (K : Set M) : Set (Model n×Model n) :=
  (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) ''
    {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1 ∧ z.1∈K}

section
variable [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma isCompact_minimizingChartParameters {a : M} {K : Set M}
    (hK : IsCompact K) (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) :
    IsCompact (minimizingChartParameters (n := n) a K) := by
  have hc : IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1 ∧ z.1∈K} :=
    (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
      (hK.isClosed.preimage (FiberBundle.continuous_proj _ _))
  exact hc.image_of_continuousOn ((continuousOn_extChartAt _).mono (fun z hz =>
    (tangent_chart_source_iff _ z).mpr (hKs hz.2)))

end

lemma mem_minimizingChartParameters {a : M} {K : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) {q : Model n×Model n}
    (hq : q∈minimizingChartParameters (n := n) a K) :
    q.1∈(extChartAt 𝓘(ℝ,Model n) a).target ∧
      ((extChartAt 𝓘(ℝ,Model n) a).symm q.1∈K ∧
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
        ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2∈
        minimizingVectors ((extChartAt 𝓘(ℝ,Model n) a).symm q.1)) := by
  obtain ⟨z,hz,rfl⟩ := hq
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hzs : z∈χ.source := (tangent_chart_source_iff _ z).mpr (hKs hz.2)
  have hb : (χ z).1∈(extChartAt 𝓘(ℝ,Model n) a).target :=
    (tangent_chart_target_iff _ _).mp (χ.map_source hzs)
  refine ⟨hb,?_⟩
  have H : (χ.symm (χ z)).1∈K ∧ (χ.symm (χ z)).2∈minimizingVectors (χ.symm (χ z)).1 := by
    rw [χ.left_inv hzs]
    exact ⟨hz.2,hz.1⟩
  rw [tangent_chart_symm_trivialization hb] at H
  exact H

lemma trivialization_mem_minimizingChartParameters {a x : M} {K : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source) (hx : x∈K)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x) :
    (extChartAt 𝓘(ℝ,Model n) a x,
      (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)∈
      minimizingChartParameters (n := n) a K :=
  ⟨⟨x,p⟩,⟨hp,hx⟩,tangent_chart_trivialization (hKs hx) p⟩

end WeakMTWTransport

end

end OAI
