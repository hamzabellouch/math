import OAI.Combinatorics.Ryser.LineCover.HighProbability

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem highConcurrency_exists_admissible
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h t : ℕ) (δ : ℝ)
    (hsparse : SparseShapes shapes D) (hδ : 0 < δ)
    (hh : 1 ≤ h) (hht : h ≤ t)
    (htR : t ≤ (coverPencil L p).card)
    (htN : t ≤ (L \ coverPencil L p).card)
    (hfailure : highFailureBound X L p shapes D h t δ < 1) :
    ∃ a : LineTuple F t, (∀ k, a k ∈ L) ∧
      AdmissibleTuple shapes D h a ∧
        ((X ∩ crossPoints a).card : ℝ) < δ * (t : ℝ) ^ 2 / 2 := by
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (hh.trans hht)
  let : Nonempty (PencilPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htR))
  let : Nonempty (ComplementPopulation L p) := Fintype.card_pos_iff.mp
    (by simpa only [Fintype.card_coe] using (lt_of_lt_of_le htpos htN))
  let : Nonempty (Fin t ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htR)
  let : Nonempty (Fin t ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin t) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe] using htN)
  let : Nonempty (Fin h ↪ PencilPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (PencilPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htR)
  let : Nonempty (Fin h ↪ ComplementPopulation L p) :=
    InjectionSampling.sample_nonempty (Fin h) (ComplementPopulation L p)
      (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_coe]
        using hht.trans htN)
  let mu := highUniformLaw L p t
  let BadSurvivors : HighSample L p t → Prop :=
    fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)
  let BadGeometry : HighSample L p t → Prop :=
    fun s => ∃ i, s.1 i ∈ highBadLines L p s.2
  let BadOccupancy : HighSample L p t → Prop := fun s => ∃ S ∈ shapes,
    S ∉ tupleShapes (highTuple L p s) ∧
      2 * D * h < (S ∩ crossPoints (highTuple L p s)).card
  have hsurvivors := high_probability_large_survivorPairs X L p δ hδ htpos
  have hgeometry := high_probability_badLines L p (t := t)
  have hoccupancy := high_probability_occupancy L p shapes D h (t := t) hsparse
  have hbound : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) ≤
      highFailureBound X L p shapes D h t δ := by
    have hu := (mu.prob_union_le BadSurvivors (fun s => BadGeometry s ∨ BadOccupancy s)).trans
      (add_le_add hsurvivors
        ((mu.prob_union_le BadGeometry BadOccupancy).trans
          (add_le_add hgeometry hoccupancy)))
    simpa only [highFailureBound, add_assoc] using hu
  have hsmall := hbound.trans_lt hfailure
  have hex : ∃ s : HighSample L p t,
      ¬ (BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) := by
    by_contra hn
    have hall (s : HighSample L p t) :
        BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s :=
      not_not.mp (fun hs => hn ⟨s, hs⟩)
    have heq : mu.prob (fun s => BadSurvivors s ∨ BadGeometry s ∨ BadOccupancy s) = 1 := by
      calc
        _ = mu.prob (fun _ => True) := by
          congr 1
          funext s
          exact propext ⟨fun _ => trivial, fun _ => hall s⟩
        _ = 1 := mu.prob_true
    rw [heq] at hsmall
    exact (lt_irrefl (1 : ℝ)) hsmall
  obtain ⟨s, hs⟩ := hex
  have havoid (i : Fin t) : s.1 i ∉ highBadLines L p s.2 := by
    intro hi
    exact hs (Or.inr (Or.inl ⟨i, hi⟩))
  have hgrid := highTuple_grid_of_avoids L p s havoid
  have hocc : ∀ S ∈ shapes, S ∉ tupleShapes (highTuple L p s) →
      (S ∩ crossPoints (highTuple L p s)).card ≤ 2 * D * h := by
    intro S hS hnot
    by_contra hlarge
    exact hs (Or.inr (Or.inr ⟨S, hS, hnot, lt_of_not_ge hlarge⟩))
  have hpair : (highSurvivorPairCount X L p s : ℝ) < δ * (t : ℝ) ^ 2 / 2 :=
    lt_of_not_ge (fun he => hs (Or.inl he))
  refine ⟨highTuple L p s, highTuple_mem L p s, ⟨hgrid.1, hgrid.2, hocc⟩, ?_⟩
  exact (Nat.cast_le.mpr (highSurvivorPoints_card_le X L p s)).trans_lt hpair

end RyserCoveringCounterexample.LineCover

end

end OAI
