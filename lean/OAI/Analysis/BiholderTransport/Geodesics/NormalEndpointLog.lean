import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

local instance tangentFiniteNormalInjective (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def minimizingEndpointChartParameters (a c : M) (K L : Set M) :
    Set (Model n×(Model n×Model n)) :=
  (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
    ((extChartAt 𝓘(ℝ,Model n) a) z.1,
      ((extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2),
       (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
          (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z).2))) ''
    {z : TangentBundle 𝓘(ℝ,Model n) M |
      z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L}

lemma isCompact_minimizingRays_between {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M |
      z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L} := by
  exact (isCompact_total_minimizingVectors (n := n) (M := M)).inter_right
    ((hK.isClosed.preimage (FiberBundle.continuous_proj _ _)).inter
      (hL.isClosed.preimage contMDiff_riemannianExp.continuous))

lemma continuousOn_riemannianExp_chart (c : M) :
    ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2))
      {z | riemannianExp z.1 z.2∈(extChartAt 𝓘(ℝ,Model n) c).source} :=
  (continuousOn_extChartAt c).comp contMDiff_riemannianExp.continuous.continuousOn
    (fun _ hz => hz)

lemma continuousOn_endpointChartParameters {a c : M} {K L : Set M}
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source) :
    ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      ((extChartAt 𝓘(ℝ,Model n) a) z.1,
        ((extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2),
         (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
            (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) z).2)))
      {z : TangentBundle 𝓘(ℝ,Model n) M |
        z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L} := by
  let S := {z : TangentBundle 𝓘(ℝ,Model n) M |
    z.2∈minimizingVectors z.1 ∧ z.1∈K ∧ riemannianExp z.1 z.2∈L}
  have hX : ContinuousOn (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)) S :=
    (continuousOn_extChartAt _).mono
      (fun z hz => (tangent_chart_source_iff _ z).mpr (hKs hz.2.1))
  have hY : ContinuousOn (fun z : TangentBundle 𝓘(ℝ,Model n) M =>
      (extChartAt 𝓘(ℝ,Model n) c) (riemannianExp z.1 z.2)) S :=
    (continuousOn_riemannianExp_chart c).mono (fun z hz => hLs hz.2.2)
  have H := hX.fst.prodMk (hY.prodMk hX.snd)
  convert H using 1
  funext z
  rw [tangent_chart_apply]

lemma isCompact_minimizingEndpointChartParameters {a c : M} {K L : Set M}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKs : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hLs : L⊆(extChartAt 𝓘(ℝ,Model n) c).source) :
    IsCompact (minimizingEndpointChartParameters (n := n) a c K L) :=
  (isCompact_minimizingRays_between hK hL).image_of_continuousOn
    (continuousOn_endpointChartParameters hKs hLs)

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)] in
lemma tangent_symmL_trivialization {a x : M}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    (p : TangentSpace 𝓘(ℝ,Model n) x) :
    (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ x
      ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p)=p :=
  Trivialization.symmL_continuousLinearMapAt _
    (by simpa only [TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx) p

lemma trivialization_mem_minimizingEndpointChartParameters {a c x : M} {K L : Set M}
    (hx : x∈K) (hxa : x∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    (hy : riemannianExp x p∈L) :
    ((extChartAt 𝓘(ℝ,Model n) a) x,
      ((extChartAt 𝓘(ℝ,Model n) c) (riemannianExp x p),
       (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).continuousLinearMapAt ℝ x p))∈
        minimizingEndpointChartParameters a c K L := by
  refine ⟨⟨x,p⟩,⟨hp,hx,hy⟩,?_⟩
  simp only [tangent_chart_trivialization hxa]

end WeakMTWTransport

end

end OAI
