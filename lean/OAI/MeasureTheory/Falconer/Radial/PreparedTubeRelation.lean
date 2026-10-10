import OAI.MeasureTheory.Falconer.Estimates.FiniteAnchorLabels
import OAI.MeasureTheory.Falconer.Measures.OriginalCoverRestriction

namespace OAI

/-! # Preparing a pointwise covered relation without losing original fiber mass -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem prepare_original_tube_relation (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G}, ∃ F : Set (Space d × Sphere d),
        MeasurableSet F ∧ F ⊆ E ∧
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        (∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) ∧
        ∀ t ∈ F, ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a.val)‖ ≤ 2*ε+δ := by
  classical
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  let C : Set (Space d × Sphere d) :=
    {t | ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ 2*ε+δ}
  have hC : MeasurableSet C := finite_tube_cover_relation_measurable G J hJ
    (fun w => (hJG w).1) _
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),E ∩ C,hE.inter hC,inter_subset_left,
    finiteAnchorLabels_measurable G J hJ,?_,?_,?_⟩
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    have he : {x | (x,w) ∈ E ∧ (x,w) ∉ E ∩ C} =
        {x | (x,w) ∈ E ∧ ∀ a ∈ J w, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} := by
      ext x
      constructor
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun a ha hp => hn ⟨hx,?_⟩⟩
        exact ⟨a,ha,hp⟩
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun ht => ?_⟩
        obtain ⟨a,ha,hp⟩ := ht.2
        exact hn a ha hp
    rw [he]
    exact hzero w
  · intro t ht
    obtain ⟨a,ha,hp⟩ := ht.2
    refine ⟨⟨a,(hJG t.2).1 ha⟩,?_,hp⟩
    exact (finiteAnchorLabels_mem G (J t.2) _).mpr ha

end Falconer

end OAI
