import OAI.Analysis.CircleDomains.Rigidity.PerturbedMeanFreeTrace
import OAI.Analysis.CircleDomains.Selection.PeriodBandGraph
import OAI.Analysis.CircleDomains.Transfer.LogarithmicCutCharts
import OAI.Analysis.CircleDomains.Selection.LiftedMeanBands
import OAI.Analysis.CircleDomains.Topology.SphereLevels

namespace OAI

/-! The actual period graph has the original mean value at every free
dust point avoided by the selected law. Vanishing smoothing error leaves
its limiting bands unchanged. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem period_graph_mean_free_value
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (D M S Free : Set Sphere) (hdense : Dense D) (b : Sphere) (hb : b ∉ Free)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ Free ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (f : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ B i)
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, f j =ᶠ[𝓝[D] x] fun y => f i y + k)
    (R : Sphere → ℝ) (hR : ∀ x ∈ Free, Tendsto R (𝓝[D] x) (𝓝 0))
    (hf : ∀ i x, x ∈ V i → f i x =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x)
    (x : Sphere) (hx : x ∈ Free) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔
      x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) = θ := by
  by_cases hxM : x ∈ M
  · have hxb : x ≠ b := fun he => hb (he ▸ hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    have hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
        (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j) := by
      intro i j x hxi hxj θ
      obtain ⟨k, hk⟩ := htrans i j x hxi hxj
      exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
    rw [periodBandGraph_on_patch D M b V f hbV hcompat hi θ]
    have hxS : x ∈ S := hVS i (subset_closure hi)
    let L : Sphere → ClosedUpperHalfPlane := fun y =>
      upperHalfPlaneClamp (logarithmicCutChart (a i) (F y))
    have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
      ((hlog i).continuousAt (mem_of_superset ((hV i).mem_nhds hi) subset_closure))
    have hproj : diskRayProjection (L x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (a i) (h1 x hxS))]
      exact logarithmicCutChart_projection (a i) (h0 x hxS)
    have havoid : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val := by
      simpa only [hproj] using hmiss x ⟨hx, hxS⟩
    have heq : f i =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y := by
      filter_upwards [nhdsWithin_le_nhds ((hV i).mem_nhds hi)] with y hy
      exact hf i y hy
    have hbnd := perturbed_mean_band_at_avoided_point hsch hsep K hK hKS η D x
      (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt havoid
      (f i) R (hR x hx) heq (hbound i) θ
    rw [hproj] at hbnd
    rw [hbnd]
  · constructor
    · exact fun h => (hxM h.1).elim
    · exact fun h => (hxM h.1).elim

end CircleDomainRigidity

end

end OAI
