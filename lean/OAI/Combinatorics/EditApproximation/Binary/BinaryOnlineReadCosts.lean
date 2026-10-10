import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReadCosts
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnlineReads

namespace OAI

/-! Online sampler arithmetic and lookup costs share one linear read factor. -/

namespace EditApproximation
namespace BinaryFraction

theorem countedPreparedActionReadWithWork_factor {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 *
        tableReadFactor R := by
  have hl := vectorMapWithWork_factor (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => onlineLinearReadWithWork_factor _ read eta kappa t _ R (fun s hs => hr s hs i))
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value, hl.1]
  apply cost_replace_factor _ _ _ _ _ hl.2 (tableReadFactor_pos R) <;> omega

theorem countedBandActionReadWithWork_factor {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 * tableReadFactor R := by
  have hm := envelopeVectorReadWithWork_factor b band initial R hi
  have hmq := (envelopeVectorReadWithWork_eq_cost b band initial R hi).1
  have hs := countedPreparedActionReadWithWork_factor
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read eta kappa band G j t R hr
  have h := Nat.add_le_add hm hs
  rw [← Nat.add_mul] at h
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hmq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem countedSampledOnlineReadWithWork_factor {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ R)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 * tableReadFactor R := by
  have hs := countedBandActionReadWithWork_factor b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ hs (tableReadFactor_pos R) <;> omega

private def onlineCostCore {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band : List (Fin M → TargetInterval n) × ℕ) (guard : Bool × ℕ)
    (sample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ) : Option Action × ℕ :=
  let setup := onlineIndexSetupWithWork H band.1
  let accepted := reduceOnlineIntegerWithWork (setup.1 ^ 80) (by
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    if guard.1 then
      let sampled := sample band.1 hband setup.1 accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

private theorem onlineCostCore_factor {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 * K)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 * K)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 * K) :
    (onlineCostCore H integer band guard sample).2 ≤
      (onlineCostCore H integer plain plainGuard plainSample).2 * K := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold onlineCostCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · apply cost_replace_factor _ _ _ _ _ hbc hK <;> omega
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    have h := Nat.add_le_add (Nat.add_le_add hbc hgc) hsample
    simp only [← Nat.add_mul] at h
    apply cost_replace_factor _ _ _ _ _ h hK <;> omega
  · have h := Nat.add_le_add hbc hgc
    rw [← Nat.add_mul] at h
    apply cost_replace_factor _ _ _ _ _ h hK <;> omega

theorem preparedOnlineReadWithWork_factor {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 * tableReadFactor R := by
  apply onlineCostCore_factor H integer
    (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) child)
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) (fun i q => (child i q).1))
    ((preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center).1.isSome,
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).2)
    ((preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1) center).1.isSome,
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1) center).2)
    (fun xs hxs G draw => countedSampledOnlineReadWithWork center b initial table eta kappa
      xs hxs G (G ^ 80) t draw)
    (fun xs hxs G draw => countedSampledOnlineWithWork center b
      (fun i q => (initial i q).1) (fun s i => (table s i).1) eta kappa xs hxs G (G ^ 80) t draw)
    (tableReadFactor R) (tableReadFactor_pos R)
  · exact (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) child R hc).1
  · exact preparedRepresentativeReadWithWork_factor parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) child R hc
  · exact congrArg Option.isSome (preparedUnskippedReadWithWork_value source target parent
      b P exponent hb hP tau (nat F) child initial R R hc hi center)
  · exact preparedUnskippedReadWithWork_factor source target parent b P exponent hb hP
      tau (nat F) child initial R hc hi center
  · intro hne G draw
    exact countedSampledOnlineReadWithWork_factor center b initial table eta kappa _ hne
      G (G ^ 80) t R draw hi (fun s hs i => ht s hs _)

end BinaryFraction
end EditApproximation

end OAI
