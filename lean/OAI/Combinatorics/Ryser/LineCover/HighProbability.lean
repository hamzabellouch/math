import OAI.Combinatorics.Ryser.LineCover.HighIncidence
import OAI.Combinatorics.Ryser.LineCover.HighDegeneracy
import OAI.Combinatorics.Ryser.LineCover.HighOccupancy
import OAI.Combinatorics.Ryser.LineCover.TwoPopulationMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RyserCoveringCounterexample.LineCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def highUniformLaw (L : Finset (AffineLine F)) (p : ProjectivePoint F) (t : ℕ)
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] : FiniteLaw (HighSample L p t) :=
  (FiniteLaw.uniform (Fin t ↪ PencilPopulation L p)).prod
    (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p))

def highFailureBound (X : Finset (Point F)) (L : Finset (AffineLine F))
    (p : ProjectivePoint F) (shapes : Finset (Finset (Point F)))
    (D h t : ℕ) (δ : ℝ) : ℝ :=
  let R := (coverPencil L p).card
  let N := (L \ coverPencil L p).card
  2 * (overlapExcess Incidence X L : ℝ) / (δ * R * N) +
    ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
    (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
      ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ))

theorem high_probability_large_survivorPairs
    (X : Finset (Point F)) (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    {t : ℕ} [Nonempty (PencilPopulation L p)] [Nonempty (ComplementPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    (δ : ℝ) (hδ : 0 < δ) (ht : 0 < t) :
    (highUniformLaw L p t).prob
        (fun s => δ * (t : ℝ) ^ 2 / 2 ≤ (highSurvivorPairCount X L p s : ℝ)) ≤
      2 * (overlapExcess Incidence X L : ℝ) /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
  have ht' : 0 < (t : ℝ) := Nat.cast_pos.mpr ht
  have hR : 0 < ((coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := PencilPopulation L p)) :
        (0 : ℝ) < Fintype.card (PencilPopulation L p))
  have hN : 0 < ((L \ coverPencil L p).card : ℝ) := by
    simpa only [Fintype.card_coe] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := ComplementPopulation L p)) :
        (0 : ℝ) < Fintype.card (ComplementPopulation L p))
  have hthreshold : 0 < δ * (t : ℝ) ^ 2 / 2 :=
    div_pos (mul_pos hδ (pow_pos ht' 2)) (by norm_num)
  have hmean : (highUniformLaw L p t).expectation
      (fun s => (highSurvivorPairCount X L p s : ℝ)) =
      (t : ℝ) ^ 2 * (highCrossPairs X L p).card /
        ((coverPencil L p).card * (L \ coverPencil L p).card : ℝ) := by
    have hcount (s : HighSample L p t) :
        highSurvivorPairCount X L p s =
          InjectionSampling.relationCount (highCrossPairs X L p) s := by
      unfold highSurvivorPairCount InjectionSampling.relationCount
      apply congrArg Finset.card
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [hcount]
    simpa only [highUniformLaw, Fintype.card_coe] using
      (InjectionSampling.expectation_relationCount (highCrossPairs X L p) (t := t))
  have hcard : ((highCrossPairs X L p).card : ℝ) ≤
      (overlapExcess Incidence X L : ℝ) :=
    Nat.cast_le.mpr (highCrossPairs_card_le X L p)
  calc
    _ ≤ (highUniformLaw L p t).expectation
        (fun s => (highSurvivorPairCount X L p s : ℝ)) / (δ * (t : ℝ) ^ 2 / 2) :=
      (highUniformLaw L p t).prob_ge_le_expectation_div _
        (fun s => Nat.cast_nonneg _) hthreshold
    _ = 2 * (highCrossPairs X L p).card /
        (δ * (coverPencil L p).card * (L \ coverPencil L p).card) := by
      rw [hmean]
      field_simp [ne_of_gt hδ, ne_of_gt hR, ne_of_gt hN, ne_of_gt ht']

    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by norm_num))
      (mul_nonneg (mul_nonneg hδ.le hR.le) hN.le)

theorem high_probability_badLines
    (L : Finset (AffineLine F)) (p : ProjectivePoint F) {t : ℕ}
    [Nonempty (PencilPopulation L p)]
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)] :
    (highUniformLaw L p t).prob (fun s => ∃ i, s.1 i ∈ highBadLines L p s.2) ≤
      ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / (coverPencil L p).card := by
  rw [highUniformLaw, InjectionSampling.prob_product_average_right]
  calc
    _ ≤ (FiniteLaw.uniform (Fin t ↪ ComplementPopulation L p)).expectation
        (fun _ => (t : ℝ) * ((t : ℝ) + (t : ℝ) * t) / (coverPencil L p).card) := by
      apply FiniteLaw.expectation_mono
      intro b
      have hcard : ((highBadLines L p b).card : ℝ) ≤ ((t + t * t : ℕ) : ℝ) :=
        Nat.cast_le.mpr (highBadLines_card_le L p b)
      rw [Nat.cast_add, Nat.cast_mul] at hcard
      calc
        _ ≤ (t : ℝ) * (highBadLines L p b).card / (coverPencil L p).card := by
          simpa only [Fintype.card_coe] using
            InjectionSampling.prob_hits_finset_le (highBadLines L p b)
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [FiniteLaw.expectation_const]
      ring

theorem high_probability_occupancy
    (L : Finset (AffineLine F)) (p : ProjectivePoint F)
    (shapes : Finset (Finset (Point F))) (D h : ℕ) {t : ℕ}
    [Nonempty (Fin t ↪ PencilPopulation L p)]
    [Nonempty (Fin t ↪ ComplementPopulation L p)]
    [Nonempty (Fin h ↪ PencilPopulation L p)]
    [Nonempty (Fin h ↪ ComplementPopulation L p)]
    (hsparse : SparseShapes shapes D) :
    (highUniformLaw L p t).prob (fun s => ∃ S ∈ shapes,
        S ∉ tupleShapes (highTuple L p s) ∧
          2 * D * h < (S ∩ crossPoints (highTuple L p s)).card) ≤
      (shapes.card : ℝ) * (t.descFactorial h : ℝ) ^ 2 *
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
        (((coverPencil L p).card.descFactorial h : ℝ) *
          ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
  let mu := highUniformLaw L p t
  have hone (S : ↥shapes) :
      mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) ≤
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
    have hcard : ((highShapePairs S.val L p).card : ℝ) ≤
        ((D * (L \ coverPencil L p).card : ℕ) : ℝ) :=
      Nat.cast_le.mpr (highShapePairs_card_le S.val L p D (hsparse S.val S.property))
    calc
      _ ≤ (t.descFactorial h : ℝ) ^ 2 * (highShapePairs S.val L p).card ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) := by
        simpa only [mu, highUniformLaw, Fintype.card_coe] using
          (InjectionSampling.prob_relation_matching_le
            (highShapePairs S.val L p) (h := h) (t := t))
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard h) (sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ mu.prob (fun s => ∃ S : ↥shapes, ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) := by
      apply mu.prob_mono
      intro s hs
      obtain ⟨S, hS, hnot, hlarge⟩ := hs
      exact ⟨⟨S, hS⟩, highShapePairs_matching_of_large
        S L p D h s (hsparse S hS) hnot hlarge⟩
    _ ≤ ∑ S : ↥shapes, mu.prob (fun s => ∃ i j : Fin h ↪ Fin t,
        ∀ k, (s.1 (i k), s.2 (j k)) ∈ highShapePairs S.val L p) :=
      mu.prob_exists_le _
    _ ≤ ∑ _S : ↥shapes,
        (t.descFactorial h : ℝ) ^ 2 *
          ((D * (L \ coverPencil L p).card : ℕ) : ℝ) ^ h /
          (((coverPencil L p).card.descFactorial h : ℝ) *
            ((L \ coverPencil L p).card.descFactorial h : ℝ)) :=
      Finset.sum_le_sum (fun S _ => hone S)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.LineCover

end

end OAI
