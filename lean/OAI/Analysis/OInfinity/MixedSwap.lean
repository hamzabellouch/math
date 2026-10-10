import OAI.Analysis.OInfinity.MixedNegative
import OAI.Analysis.OInfinity.BufferedTail

namespace OAI

/-! # The exact three-summand permutation in mixed stabilization

The first two target ranges are exchanged by an explicit connected
self-adjoint unitary. The negative corner is fixed pointwise. This gives
the literal permutation used in cancellation, with the complementary
representation still present.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def mixedStabilizedRow (s t : ℕ → E) (i : ℕ) : E :=
  t 0 * s i * star (t 0) + canonicalNegativeRow t i

def mixedSwappedRow (s t : ℕ → E) (i : ℕ) : E :=
  t 0 * t i * star (t 0) + mixedNegativeRow s t i

private lemma mixed_swap_data (t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) :
    let a := t 1 * star (t 0)
    a * star a * a = a ∧ a * a = 0 ∧
      partialIsometrySwap a = t 1 * star (t 0) + t 0 * star (t 1) +
        canonicalNegativeProjection t := by
  intro a
  have h00 : star (t 0) * t 0 = 1 := by simpa only [ite_true] using ht 0 0
  have h11 : star (t 1) * t 1 = 1 := by simpa only [ite_true] using ht 1 1
  have h01 : star (t 0) * t 1 = 0 := by simpa using ht 0 1
  have ha : star a = t 0 * star (t 1) := by simp only [a, star_mul, star_star]
  have hi : star a * a = t 0 * star (t 0) := by
    rw [ha]
    change (t 0 * star (t 1)) * (t 1 * star (t 0)) = _
    calc
      _ = t 0 * (star (t 1) * t 1) * star (t 0) := by noncomm_ring
      _ = _ := by rw [h11, mul_one]
  have hf : a * star a = t 1 * star (t 1) := by
    rw [ha]
    change (t 1 * star (t 0)) * (t 0 * star (t 1)) = _
    calc
      _ = t 1 * (star (t 0) * t 0) * star (t 1) := by noncomm_ring
      _ = _ := by rw [h00, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc, hi]
    change (t 1 * star (t 0)) * (t 0 * star (t 0)) = t 1 * star (t 0)
    calc
      _ = t 1 * (star (t 0) * t 0) * star (t 0) := by noncomm_ring
      _ = _ := by rw [h00, mul_one]
  · change (t 1 * star (t 0)) * (t 1 * star (t 0)) = 0
    calc
      _ = t 1 * (star (t 0) * t 1) * star (t 0) := by noncomm_ring
      _ = 0 := by rw [h01, mul_zero, zero_mul]
  · rw [partialIsometrySwap, hi, hf, ha]
    change t 1 * star (t 0) + t 0 * star (t 1) +
      (1 - t 0 * star (t 0) - t 1 * star (t 1)) = _
    rw [canonicalNegativeProjection, canonicalTailProjection_succ,
      canonicalTailProjection_succ, canonicalTailProjection_zero]

/-- The actual connected flip interchanges the two full ranges and fixes
the entire remaining corner, rather than merely preserving its projection. -/
lemma exists_connected_mixed_swap [Nontrivial E] (t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) :
    ∃ u : unitary E, Joined 1 u ∧ star (u : E) = (u : E) ∧
      (u : E) * t 0 = t 1 ∧ (u : E) * t 1 = t 0 ∧
      (u : E) * canonicalNegativeProjection t = canonicalNegativeProjection t ∧
      canonicalNegativeProjection t * (u : E) = canonicalNegativeProjection t ∧
      ∀ i, (u : E) * (t (i + 2) * canonicalNegativeProjection t) =
        t (i + 2) * canonicalNegativeProjection t := by
  obtain ⟨ha, haa, he⟩ := mixed_swap_data t ht
  let a := t 1 * star (t 0)
  let u := partialIsometrySwapUnitary a ha haa
  have hue : (u : E) = t 1 * star (t 0) + t 0 * star (t 1) +
      canonicalNegativeProjection t := he
  have hus : star (u : E) = (u : E) := partialIsometrySwap_star a
  have h00 : star (t 0) * t 0 = 1 := by simpa only [ite_true] using ht 0 0
  have h11 : star (t 1) * t 1 = 1 := by simpa only [ite_true] using ht 1 1
  have h01 : star (t 0) * t 1 = 0 := by simpa using ht 0 1
  have h10 : star (t 1) * t 0 = 0 := by simpa using ht 1 0
  have hp0 : canonicalNegativeProjection t * t 0 = 0 :=
    (canonicalTailProjection_mul_generator t ht 2 0).trans (ite_eq_left (by omega))
  have hp1 : canonicalNegativeProjection t * t 1 = 0 :=
    (canonicalTailProjection_mul_generator t ht 2 1).trans (ite_eq_left (by omega))
  have h0p : star (t 0) * canonicalNegativeProjection t = 0 :=
    (canonicalTailProjection_generator_star t ht 2 0).trans (ite_eq_left (by omega))
  have h1p : star (t 1) * canonicalNegativeProjection t = 0 :=
    (canonicalTailProjection_generator_star t ht 2 1).trans (ite_eq_left (by omega))
  have hp : star (canonicalNegativeProjection t) = canonicalNegativeProjection t :=
    canonicalTailProjection_star t 2
  have hpp : canonicalNegativeProjection t * canonicalNegativeProjection t =
      canonicalNegativeProjection t := canonicalTailProjection_idempotent t ht 2
  have hup : (u : E) * canonicalNegativeProjection t = canonicalNegativeProjection t := by
    rw [hue, add_mul, add_mul, mul_assoc, h0p, mul_assoc, h1p]
    simpa only [mul_zero, zero_add] using hpp
  refine ⟨u, partialIsometrySwapUnitary_joined a ha haa, hus, ?_, ?_, hup, ?_, ?_⟩
  · rw [hue, add_mul, add_mul, mul_assoc, h00, mul_assoc, h10, hp0]
    simp only [mul_one, mul_zero, add_zero]
  · rw [hue, add_mul, add_mul, mul_assoc, h01, mul_assoc, h11, hp1]
    simp only [mul_one, mul_zero, zero_add, add_zero]
  · simpa only [star_mul, hp, hus] using congrArg star hup
  · intro i
    have h0i : star (t 0) * t (i + 2) = 0 := by rw [ht, ite_eq_right (by omega)]
    have h1i : star (t 1) * t (i + 2) = 0 := by rw [ht, ite_eq_right (by omega)]
    have hpi : canonicalNegativeProjection t * t (i + 2) = t (i + 2) :=
      (canonicalTailProjection_mul_generator t ht 2 (i + 2)).trans (ite_eq_right (by omega))
    rw [hue, add_mul, add_mul]
    calc
      _ = t 1 * (star (t 0) * t (i + 2)) * canonicalNegativeProjection t +
          t 0 * (star (t 1) * t (i + 2)) * canonicalNegativeProjection t +
          (canonicalNegativeProjection t * t (i + 2)) * canonicalNegativeProjection t := by
            noncomm_ring
      _ = _ := by rw [h0i, h1i, hpi]; simp only [mul_zero, zero_mul, zero_add]

/-- A fixed connected unitary performs the full three-summand permutation,
for every source row and every generator simultaneously. -/
lemma exists_connected_mixed_stabilization_permutation [Nontrivial E] (t : ℕ → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) :
    ∃ u : unitary E, Joined 1 u ∧
      ∀ (s : ℕ → E) i, (u : E) * mixedStabilizedRow s t i * star (u : E) =
        mixedSwappedRow s t i := by
  obtain ⟨u, hu, hus, hu0, hu1, hup, _hpu, hut⟩ := exists_connected_mixed_swap t ht
  have h0u : star (t 0) * star (u : E) = star (t 1) := by
    simpa only [star_mul] using congrArg star hu0
  have h1u : star (t 1) * star (u : E) = star (t 0) := by
    simpa only [star_mul] using congrArg star hu1
  have hpu : canonicalNegativeProjection t * star (u : E) = canonicalNegativeProjection t := by
    simpa only [hus] using _hpu
  refine ⟨u, hu, fun s i => ?_⟩
  change (u : E) * (t 0 * s i * star (t 0) +
    (t 1 * t i * star (t 1) + t (i + 2) * canonicalNegativeProjection t)) * star (u : E) =
      t 0 * t i * star (t 0) +
        (t 1 * s i * star (t 1) + t (i + 2) * canonicalNegativeProjection t)
  have htail : (u : E) * (t (i + 2) * canonicalNegativeProjection t) * star (u : E) =
      t (i + 2) * canonicalNegativeProjection t := by
    rw [hut, mul_assoc, hpu]
  calc
    _ = ((u : E) * t 0) * s i * (star (t 0) * star (u : E)) +
        ((u : E) * t 1) * t i * (star (t 1) * star (u : E)) +
        (u : E) * (t (i + 2) * canonicalNegativeProjection t) * star (u : E) := by
          noncomm_ring
    _ = _ := by rw [hu0, hu1, h0u, h1u, htail]; abel

end WeakPureInfiniteness

end

end OAI
