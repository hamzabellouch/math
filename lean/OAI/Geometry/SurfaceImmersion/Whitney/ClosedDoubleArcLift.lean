import OAI.Geometry.SurfaceImmersion.Whitney.OpenDoubleArcLift
import OAI.Geometry.SurfaceImmersion.Geometry.OpenIntervalExtension
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSingletonFiber

namespace OAI

/-! An ordered lift of a double arc extends continuously to its two
crosscap endpoints, since each diagonal fiber is a singleton. -/
noncomputable section
open Set Filter Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]

theorem closed_double_arc_lift (p q : M)
    (γ : Path (unorderedPair (p,p)) (unorderedPair (q,q)))
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ Γ : Path (p,p) (q,q), ∀ t, unorderedPair (Γ t) = γ t := by
  obtain ⟨F,hF⟩ := open_double_arc_lift γ.toContinuousMap hγ
  let G := openIntervalExtension F (p,p) (q,q)
  have hG0 : G 0 = (p,p) := openIntervalExtension_zero F _ _
  have hG1 : G 1 = (q,q) := openIntervalExtension_one F _ _
  have hG : ∀ t, unorderedPair (G t) = γ t := by
    intro t
    by_cases h0 : t = 0
    · subst t
      rw [hG0,γ.source]
    by_cases h1 : t = 1
    · subst t
      rw [hG1,γ.target]
    have ht := (intervalInteriorPoint t h0 h1).property
    rw [show G t = F ⟨t.val,ht⟩ from openIntervalExtension_interior F _ _ t ht]
    exact hF ⟨t.val,ht⟩
  have hbase : Continuous (unorderedPair ∘ G) := by
    have he : unorderedPair ∘ G = γ := funext hG
    rw [he]
    exact γ.continuous
  have hcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases h0 : t = 0
    · subst t
      change Tendsto G (𝓝 0) (𝓝 (G 0))
      rw [hG0]
      apply tendsto_of_comp_singleton_fiber unorderedPair_continuous
        (fun z hz => (unorderedPair_diagonal_iff z p).mp hz)
      have hc : Tendsto (unorderedPair ∘ G) (𝓝 (0:I)) (𝓝 (unorderedPair (G 0))) := hbase.continuousAt
      simpa only [hG0] using hc
    by_cases h1 : t = 1
    · subst t
      change Tendsto G (𝓝 1) (𝓝 (G 1))
      rw [hG1]
      apply tendsto_of_comp_singleton_fiber unorderedPair_continuous
        (fun z hz => (unorderedPair_diagonal_iff z q).mp hz)
      have hc : Tendsto (unorderedPair ∘ G) (𝓝 (1:I)) (𝓝 (unorderedPair (G 1))) := hbase.continuousAt
      simpa only [hG1] using hc
    · have ht := (intervalInteriorPoint t h0 h1).property
      have hU : IsOpen {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} :=
        isOpen_Ioo.preimage continuous_subtype_val
      exact (openIntervalExtension_continuousOn F F.continuous _ _).continuousAt (hU.mem_nhds ht)
  exact ⟨⟨⟨G,hcont⟩,hG0,hG1⟩,hG⟩

theorem embedded_closed_double_arc_lift (p q : M)
    (γ : Path (unorderedPair (p,p)) (unorderedPair (q,q))) (hinj : Function.Injective γ)
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ Γ : Path (p,p) (q,q), IsClosedEmbedding Γ ∧ ∀ t, unorderedPair (Γ t) = γ t := by
  obtain ⟨Γ,hΓ⟩ := closed_double_arc_lift p q γ hγ
  have hΓinj : Function.Injective Γ := by
    intro s t h
    apply hinj
    rw [← hΓ s,← hΓ t,h]
  exact ⟨Γ,Γ.continuous.isClosedEmbedding hΓinj,hΓ⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
