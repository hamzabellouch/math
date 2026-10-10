import OAI.Combinatorics.EditApproximation.Binary.BinaryBandActionReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnline

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

private def preparedOnlineReadCore {n M : ℕ} {Action : Type*} (H integer : ℕ)
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

private theorem preparedOnlineReadCore_compare {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (B C E : ℕ) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 + B)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 + C)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).1 = (plainSample plain.1 hne G draw).1 ∧
      (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 + E) :
    (preparedOnlineReadCore H integer band guard sample).1 =
      (preparedOnlineReadCore H integer plain plainGuard plainSample).1 ∧
    (preparedOnlineReadCore H integer band guard sample).2 ≤
      (preparedOnlineReadCore H integer plain plainGuard plainSample).2 + (B + C + E) := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold preparedOnlineReadCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · exact ⟨rfl, by omega⟩
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    exact ⟨congrArg some hsample.1, by omega⟩
  · exact ⟨rfl, by omega⟩

def preparedOnlineReadWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let band := preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let G := setup.1
  let accepted := reduceOnlineIntegerWithWork (G ^ 80) (by
    dsimp only [G, setup]
    rw [onlineIndexSetupWithWork_value]
    positivity) integer
  if hband : band.1 = [] then (none, band.2 + setup.2 + accepted.2 + 1) else
    let guard := preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center
    if guard.1.isSome then
      let sampled := countedSampledOnlineReadWithWork center b initial table eta kappa band.1 hband
        G (G ^ 80) t accepted.1
      (some sampled.1, band.2 + setup.2 + accepted.2 + guard.2 + sampled.2 + 2)
    else (none, band.2 + setup.2 + accepted.2 + guard.2 + 1)

def preparedOnlineReadExtra {nx n : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (center : TargetInterval n) (b P exponent R t : ℕ) (tau : BinaryFraction)
    (child : Fin M → TargetInterval n → BinaryFraction) : ℕ :=
  let band := (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo exponent) child).1
  2 * representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
    3 * (M * (band.length * (R + 3))) +
    (listedBandCoordinates band).length * ((3 * t + 1) * R)

theorem preparedOnlineReadWithWork_eq_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).1 =
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).1 ∧
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 +
      preparedOnlineReadExtra M parent center b P exponent R t tau (fun i q => (child i q).1) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) child R hc
  have hguard := preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have hguardCost := preparedUnskippedReadWithWork_cost source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have h := preparedOnlineReadCore_compare H integer
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
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      2 * (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3))))
    (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3)) +
      (listedBandCoordinates (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1).length * ((3 * t + 1) * R))
    hband.1 hband.2 (congrArg Option.isSome hguard) (by omega)
    (fun hne G draw => by
      simpa only [Nat.add_assoc] using countedSampledOnlineReadWithWork_eq_cost center b initial table eta kappa
        _ hne G (G ^ 80) t R R draw hi (fun s hs i => ht s hs _))
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> first
  | rfl
  | (dsimp only [preparedOnlineReadExtra, preparedOnlineWithWork, preparedOnlineReadCore]; ring)

end BinaryFraction
end EditApproximation

end OAI
