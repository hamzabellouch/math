import OAI.Combinatorics.ProgressionColoring.LabelCounts

namespace OAI

universe uAlpha uBeta uWord uU uV

namespace QuantitativeVanDerWaerden

/-- Decode two independent coordinate systems without identifying their scalar
output types. This is also the global full-word product estimate. -/
theorem card_decoded_twoSystems_le {D B : ℕ} {α : Type uAlpha} {β : Type uBeta} {Word : Type uWord}
    [DecidableEq Word] (firstS : Fin D → Finset α) (secondS : Fin D → Finset β)
    (decode : ((Fin D → α) × (Fin D → β)) → Word)
    (hfirst : ∀ i, (firstS i).card ≤ B) (hsecond : ∀ i, (secondS i).card ≤ B) :
    (((coordinateFamily firstS).product (coordinateFamily secondS)).image decode).card ≤
      B ^ (2 * D) := by
  classical
  calc
    _ ≤ ((coordinateFamily firstS).product (coordinateFamily secondS)).card :=
      Finset.card_image_le
    _ = (coordinateFamily firstS).card * (coordinateFamily secondS).card :=
      Finset.card_product _ _
    _ ≤ B ^ D * B ^ D := Nat.mul_le_mul
      (card_coordinateFamily_le firstS hfirst)
      (card_coordinateFamily_le secondS hsecond)
    _ = B ^ (2 * D) := by rw [two_mul, pow_add]

/-- Literal `(step vector, recorded word)` incidences, retaining the step vector
even when two different steps yield the same word. The two scalar systems have
their actual different output types. -/
noncomputable def anchoredIncidences {D h : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V)) :
    Finset ((Fin D → Fin h) × (Fin h → Option (FullLabel D U V))) := by
  classical
  exact Finset.univ.biUnion fun t => Finset.univ.biUnion fun z =>
    ((coordinateFamily (firstS t z)).product (coordinateFamily (secondS t z))).image
      (fun p => (t, assembleWord p.1 p.2))

theorem mem_anchoredIncidences_of_mem {D h : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (t : Fin D → Fin h) (z : Fin h)
    (first : Fin D → Fin h → U) (second : Fin D → Fin h → Option V)
    (hfirst : ∀ i, first i ∈ firstS t z i)
    (hsecond : ∀ i, second i ∈ secondS t z i) :
    (t, assembleWord first second) ∈ anchoredIncidences firstS secondS := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨z, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨(first, second), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Fintype.mem_piFinset.mpr hfirst
  · exact Fintype.mem_piFinset.mpr hsecond

theorem card_anchoredIncidences_le {D h B : ℕ} {U : Type uU} {V : Type uV}
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (hfirst : ∀ t z i, (firstS t z i).card ≤ B)
    (hsecond : ∀ t z i, (secondS t z i).card ≤ B) :
    (anchoredIncidences firstS secondS).card ≤ h ^ (D + 1) * B ^ (2 * D) := by
  classical
  unfold anchoredIncidences
  calc
    _ ≤ (Finset.univ : Finset (Fin D → Fin h)).card * (h * B ^ (2 * D)) := by
      apply Finset.card_biUnion_le_card_mul
      intro t _
      calc
        _ ≤ (Finset.univ : Finset (Fin h)).card * B ^ (2 * D) := by
          apply Finset.card_biUnion_le_card_mul
          intro z _
          exact card_decoded_twoSystems_le (firstS t z) (secondS t z)
            (fun p => (t, assembleWord p.1 p.2)) (hfirst t z) (hsecond t z)
        _ = h * B ^ (2 * D) := by simp
    _ = h ^ (D + 1) * B ^ (2 * D) := by
      simp [pow_succ, Nat.mul_assoc]

theorem card_anchoredIncidences_polynomial_le {D h : ℕ} {U : Type uU} {V : Type uV}
    (hD : 0 < D) (hh : 0 < h)
    (firstS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → U))
    (secondS : (Fin D → Fin h) → Fin h → Fin D → Finset (Fin h → Option V))
    (hfirst : ∀ t z i, (firstS t z i).card ≤ 16 * (16004 * D * h + 1) ^ 6)
    (hsecond : ∀ t z i, (secondS t z i).card ≤ 16 * (16004 * D * h + 1) ^ 6) :
    (anchoredIncidences firstS secondS).card ≤ (16005 * D * h) ^ (14 * D) :=
  (card_anchoredIncidences_le firstS secondS hfirst hsecond).trans
    (anchored_polynomial_estimate D h hD hh)

end QuantitativeVanDerWaerden

end OAI
