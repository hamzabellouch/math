import OAI.MeasureTheory.Falconer.Radial.MeasurableTubeCover

namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

noncomputable def finiteAnchorLabels (G J : Finset (Space d)) : Finset {a // a ∈ G} := by
  classical
  exact J.subtype (fun a => a ∈ G)

theorem finiteAnchorLabels_mem (G J : Finset (Space d)) (a : {a // a ∈ G}) :
    a ∈ finiteAnchorLabels G J ↔ a.val ∈ J := by
  classical
  exact Finset.mem_subtype

theorem finiteAnchorLabels_card (G J : Finset (Space d)) (hJG : J ⊆ G) :
    (finiteAnchorLabels G J).card = J.card := by
  classical
  rw [finiteAnchorLabels,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun a ha => hJG ha)

theorem finiteAnchorLabels_measurable (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (a : {a // a ∈ G}) :
    MeasurableSet {w | a ∈ finiteAnchorLabels G (J w)} := by
  simpa only [finiteAnchorLabels_mem] using hJ a.val

theorem finiteAnchorLabels_uncovered (G : Finset (Space d)) (J : Finset (Space d))
    (hJG : J ⊆ G) (w : Sphere d) (R : ℝ) (x : Space d) :
    (∀ a ∈ finiteAnchorLabels G J, ¬‖perpendicularPart (w:Space d) (x-a.val)‖ ≤ R) ↔
      ∀ a ∈ J, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ R := by
  constructor
  · intro h a ha
    exact h ⟨a,hJG ha⟩ ((finiteAnchorLabels_mem G J _).mpr ha)
  · intro h a ha
    exact h a.val ((finiteAnchorLabels_mem G J _).mp ha)

theorem original_finite_label_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G},
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a.val)‖ ≤ 2*ε+δ} = 0 := by
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),?_,?_,?_⟩
  · exact finiteAnchorLabels_measurable G J hJ
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    simpa only [finiteAnchorLabels_uncovered G (J w) (hJG w).1] using hzero w

end Falconer

end OAI
