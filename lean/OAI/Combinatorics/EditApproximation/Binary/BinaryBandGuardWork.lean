import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard
import OAI.Combinatorics.EditApproximation.Refinement.ComputedBands
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact finite band predicates evaluated on stored Boolean fractions.
The cut tests use the actual finite prefix minimum; the other tests are
Boolean comparisons of the actual interval endpoints. -/

namespace EditApproximation

open Finset



@[simp] theorem naturalEqualWithWork_value (a b : ℕ) :
    (naturalEqualWithWork a b).1 = true ↔ a = b := by
  simp only [naturalEqualWithWork, decide_eq_true_eq, binaryNaturalCompareWithWork_eq]

theorem naturalEqualWithWork_cost (a b B : ℕ) (ha : Nat.size a ≤ B) (hb : Nat.size b ≤ B) :
    (naturalEqualWithWork a b).2 ≤ 8 * B + 2 := by
  have h := binaryNaturalCompareWithWork_cost a b
  change (binaryNaturalCompareWithWork a b).2 + 1 ≤ _
  omega



@[simp] theorem zeroConnectionWithWork_value {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) :
    (zeroConnectionWithWork start states finish).1 = true ↔
      connectionBudget start states finish = 0 := by
  induction states generalizing start with
  | nil =>
    change (naturalEqualWithWork start finish).1 = true ↔ Nat.dist start finish = 0
    exact (naturalEqualWithWork_value start finish).trans
      ⟨Nat.dist_eq_zero, Nat.eq_of_dist_eq_zero⟩
  | cons state rest ih =>
    change ((naturalEqualWithWork start state.lo).1 &&
      (zeroConnectionWithWork state.hi rest finish).1) = true ↔
        Nat.dist start state.lo + connectionBudget state.hi rest finish = 0
    rw [Bool.and_eq_true, naturalEqualWithWork_value, ih, Nat.add_eq_zero_iff]
    constructor
    · rintro ⟨hs, ht⟩
      exact ⟨Nat.dist_eq_zero hs, ht⟩
    · rintro ⟨hs, ht⟩
      exact ⟨Nat.eq_of_dist_eq_zero hs, ht⟩

theorem zeroConnectionWithWork_cost {n : ℕ} (start finish : ℕ)
    (states : List (TargetInterval n)) (B : ℕ)
    (hs : Nat.size start ≤ B) (hf : Nat.size finish ≤ B)
    (he : ∀ s ∈ states, Nat.size s.lo ≤ B ∧ Nat.size s.hi ≤ B) :
    (zeroConnectionWithWork start states finish).2 ≤ (states.length + 1) * (8 * B + 3) := by
  induction states generalizing start with
  | nil =>
    have h := naturalEqualWithWork_cost start finish B hs hf
    simpa only [zeroConnectionWithWork, List.length_nil, zero_add, one_mul] using
      h.trans (by omega : 8 * B + 2 ≤ 8 * B + 3)
  | cons state rest ih =>
    have hstate := he state List.mem_cons_self
    have hc := naturalEqualWithWork_cost start state.lo B hs hstate.1
    have ht := ih state.hi hstate.2 (fun s h => he s (List.mem_cons_of_mem _ h))
    change _ + _ + 1 ≤ _
    simp only [List.length_cons]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

/-- Construct a translated endpoint by the actual binary subtract/add routines. -/


@[simp] theorem translatedEndpointWithWork_value (reference root endpoint : ℕ) (h : root ≤ endpoint) :
    (translatedEndpointWithWork reference root endpoint).1 = reference + (endpoint - root) := by
  simp only [translatedEndpointWithWork, binaryNaturalAddWithWork_value,
    binaryNaturalSubtractWithWork_value endpoint root h]

theorem translatedEndpointWithWork_cost (reference root endpoint B : ℕ)
    (h : root ≤ endpoint) (hr : Nat.size reference ≤ B)
    (hroot : Nat.size root ≤ B) (he : Nat.size endpoint ≤ B) :
    (translatedEndpointWithWork reference root endpoint).2 ≤ 36 * B + 4 := by
  have hd := binaryNaturalSubtractWithWork_cost endpoint root
  have ha := binaryNaturalAddWithWork_cost reference
    (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1)
  have hw : Nat.size (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1) ≤ B := by
    rw [binaryNaturalSubtractWithWork_value endpoint root h]
    exact (Nat.size_le_size (Nat.sub_le endpoint root)).trans he
  change _ + _ + 2 ≤ _
  omega

namespace BinaryFraction

private theorem nat_dist_cast (a b : ℕ) : (Nat.dist a b : ℚ) = |(a : ℚ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]



@[simp] theorem naturalDistanceLeWithWork_value (a b radius : ℕ) :
    (naturalDistanceLeWithWork a b radius).1 = true ↔ Nat.dist a b ≤ radius := by
  simp only [naturalDistanceLeWithWork, leWithWork_value, distanceWithWork_value, nat_value]
  rw [← nat_dist_cast]
  constructor <;> intro h <;> exact_mod_cast h

def naturalDistanceBitBudget (B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + 2 + (1000 * (8 * B + 7) ^ 2 + 1) + 3 * B + 3

theorem naturalDistanceLeWithWork_cost (a b radius B : ℕ)
    (ha : Nat.size a + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hr : Nat.size radius + 2 ≤ B) :
    (naturalDistanceLeWithWork a b radius).2 ≤ naturalDistanceBitBudget B := by
  have hdw := distanceWithWork_width (nat a) (nat b) B
    ((nat_width_le a).trans ha) ((nat_width_le b).trans hb)
  have hd := distanceWithWork_cost (nat a) (nat b) B
    ((nat_width_le a).trans ha) ((nat_width_le b).trans hb)
  have hc := leWithWork_cost (distanceWithWork (nat a) (nat b)).1 (nat radius)
    (8 * B + 6) hdw ((nat_width_le radius).trans (by omega))
  simp only [Nat.add_assoc, Nat.reduceAdd] at hc
  change _ + _ + Nat.size a + Nat.size b + Nat.size radius + 3 ≤ _
  unfold naturalDistanceBitBudget
  omega

def cutGuardWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) : Bool × ℕ :=
  if j.val = 0 then (true, 1) else
    let shift := subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)
    let offset := subWithWork (nat r.lo) (nat parent.lo)
    let prediction := prefixMinimumWithWork parent r actions hne child j.val shift.1
    let result := affineErrorWithWork shift.1 offset.1 velocity prediction.1 tolerance
    (result.1, shift.2 + offset.2 + prediction.2 + result.2 +
      Nat.size (states j).lo + Nat.size (sourceChild parent j).lo + Nat.size r.lo + Nat.size parent.lo + 5)

@[simp] theorem cutGuardWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) :
    (cutGuardWithWork parent r actions hne child states velocity tolerance j).1 = true ↔
      (0 < j.val → |bandCutShift parent states j - ((r.lo : ℚ) - parent.lo) - velocity.value *
        rationalWidePrefixMinimum parent r actions hne (fun i q => (child i q).value)
          j.val (bandCutShift parent states j)| ≤ tolerance.value) := by
  by_cases hj : j.val = 0
  · simp [cutGuardWithWork, hj]
  · rw [cutGuardWithWork, ite_eq_right hj]
    dsimp only
    rw [affineErrorWithWork_value]
    simp only [subWithWork_value, nat_value, prefixMinimumWithWork_value, bandCutShift]
    constructor
    · intro h _
      exact h
    · intro h
      exact h (Nat.pos_of_ne_zero hj)

def cutGuardWordBudget (M j B : ℕ) : ℕ :=
  prefixWordBudget M j (8 * B + 6) + 76 * B + 50

def cutGuardBitBudget (M j v B : ℕ) : ℕ :=
  2 * (6000 * (B + 1) ^ 2 + 1) +
    prefixMinimumBitBudget M j v (8 * B + 6) +
    affineGuardBitBudget (cutGuardWordBudget M j B) + 4 * B + 6

theorem cutGuardWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) (B : ℕ)
    (hvel : velocity.width ≤ B) (htol : tolerance.width ≤ 64 * B + 44)
    (hr : Nat.size r.lo + 2 ≤ B) (hp : Nat.size parent.lo + 2 ≤ B)
    (hs : Nat.size (states j).lo + 2 ≤ B)
    (hc : Nat.size (sourceChild parent j).lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j.val) + 2 ≤ B)
    (hstates : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B) :
    (cutGuardWithWork parent r actions hne child states velocity tolerance j).2 ≤
      cutGuardBitBudget M j.val actions.length B := by
  by_cases hj : j.val = 0
  · simp only [cutGuardWithWork, hj, ↓reduceIte]
    unfold cutGuardBitBudget
    omega
  · have hshift := subWithWork_width (nat (states j).lo) (nat (sourceChild parent j).lo) B
      ((nat_width_le _).trans hs) ((nat_width_le _).trans hc)
    have hoffset := subWithWork_width (nat r.lo) (nat parent.lo) B
      ((nat_width_le _).trans hr) ((nat_width_le _).trans hp)
    have hshiftCost := subWithWork_cost (nat (states j).lo) (nat (sourceChild parent j).lo) B
      ((nat_width_le _).trans hs) ((nat_width_le _).trans hc)
    have hoffsetCost := subWithWork_cost (nat r.lo) (nat parent.lo) B
      ((nat_width_le _).trans hr) ((nat_width_le _).trans hp)
    have hlarge : B ≤ 8 * B + 6 := by omega
    obtain ⟨hpred, hpredCost⟩ := prefixMinimumWithWork_bounds parent r actions hne child j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 (8 * B + 6)
      hshift (hr.trans hlarge) (hcut.trans hlarge)
      (fun action ha i => ⟨(hstates action ha i).1.trans hlarge,
        (hstates action ha i).2.trans hlarge⟩)
      (fun action ha i => (hchild action ha i).trans hlarge)
    have herr := affineErrorWithWork_cost
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1
      (subWithWork (nat r.lo) (nat parent.lo)).1 velocity
      (prefixMinimumWithWork parent r actions hne child j.val
        (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1).1
      tolerance (cutGuardWordBudget M j.val B)
      (by unfold cutGuardWordBudget; omega) (by unfold cutGuardWordBudget; omega)
      (by unfold cutGuardWordBudget; omega) (by unfold cutGuardWordBudget; omega)
      (by unfold cutGuardWordBudget; omega)
    simp only [cutGuardWithWork, hj, ↓reduceIte]
    unfold cutGuardBitBudget
    omega

def bandPredicateWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny) : Bool × ℕ :=
  let connection := zeroConnectionWithWork r.lo (List.ofFn states) r.hi
  let anchors := allWithWork (fun i : Fin M =>
    let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
    let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
    let radius := binaryNaturalMulWithWork 6 b
    let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
    let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
    (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3)) (List.finRange M)
  let tolerance := bandToleranceWithWork tau theta b M
  let cuts := allWithWork (cutGuardWithWork parent r actions hne child states velocity tolerance.1)
    (List.finRange M)
  (connection.1 && anchors.1 && cuts.1, connection.2 + anchors.2 + tolerance.2 + cuts.2 + 4)

@[simp] theorem bandPredicateWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny) :
    (bandPredicateWithWork parent r b tau theta velocity actions hne child states).1 = true ↔
      bandActionPredicate parent r b tau.value theta.value velocity.value actions hne
        (fun i q => (child i q).value) states := by
  have hlo (i : Fin M) : parent.lo ≤ (sourceChild parent i).lo := Nat.le_add_right _ _
  have hhi (i : Fin M) : parent.lo ≤ (sourceChild parent i).hi := Nat.le_add_right _ _
  simp only [bandPredicateWithWork, Bool.and_eq_true, zeroConnectionWithWork_value,
    allWithWork_value, naturalDistanceLeWithWork_value, cutGuardWithWork_value,
    translatedEndpointWithWork_value _ _ _ (hlo _), translatedEndpointWithWork_value _ _ _ (hhi _),
    binaryNaturalMulWithWork_value, bandToleranceWithWork_value, List.mem_finRange, forall_true_left,
    endpointActionConnection, bandActionPredicate]
  exact and_assoc

def anchorGuardBitBudget (B : ℕ) : ℕ :=
  2 * (36 * B + 4) + 80 * (B + 4) + 2 * naturalDistanceBitBudget B + 3

def bandPredicateBitBudget (M B C : ℕ) : ℕ :=
  (M + 1) * (8 * B + 3) + M * (anchorGuardBitBudget B + 3) +
    bandToleranceBitBudget B + M * (C + 3) + 4

theorem bandPredicateWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (states : Fin M → TargetInterval ny)
    (B C : ℕ) (hstatesMem : states ∈ actions)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B) (hvel : velocity.width ≤ B)
    (hb : Nat.size b + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hr : Nat.size r.lo + 2 ≤ B) (hrhi : Nat.size r.hi + 2 ≤ B)
    (hp : Nat.size parent.lo + 2 ≤ B)
    (hsource : ∀ i : Fin M, Nat.size (sourceChild parent i).lo + 2 ≤ B ∧
      Nat.size (sourceChild parent i).hi + 2 ≤ B)
    (hanchor : ∀ i : Fin M, Nat.size (r.lo + ((sourceChild parent i).lo - parent.lo)) + 2 ≤ B ∧
      Nat.size (r.lo + ((sourceChild parent i).hi - parent.lo)) + 2 ≤ B)
    (hradius : Nat.size (6 * b) + 2 ≤ B)
    (hstates : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B)
    (hC : ∀ j : Fin M, cutGuardBitBudget M j.val actions.length B ≤ C) :
    (bandPredicateWithWork parent r b tau theta velocity actions hne child states).2 ≤
      bandPredicateBitBudget M B C := by
  have hstate := hstates states hstatesMem
  have hlo (i : Fin M) : parent.lo ≤ (sourceChild parent i).lo := Nat.le_add_right _ _
  have hhi (i : Fin M) : parent.lo ≤ (sourceChild parent i).hi := Nat.le_add_right _ _
  have hconn := zeroConnectionWithWork_cost r.lo r.hi (List.ofFn states) B (by omega) (by omega) (by
    intro state hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    have := hstate i
    omega)
  have hanchorCost (i : Fin M) :
      (let leftAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo
       let rightAnchor := translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi
       let radius := binaryNaturalMulWithWork 6 b
       let left := naturalDistanceLeWithWork leftAnchor.1 (states i).lo (bitWordValue radius.1)
       let right := naturalDistanceLeWithWork rightAnchor.1 (states i).hi (bitWordValue radius.1)
       (left.1 && right.1, leftAnchor.2 + rightAnchor.2 + radius.2 + left.2 + right.2 + 3)).2 ≤
        anchorGuardBitBudget B := by
    have hl := translatedEndpointWithWork_cost r.lo parent.lo (sourceChild parent i).lo B
      (hlo i) (by omega) (by omega) (by have := hsource i; omega)
    have hh := translatedEndpointWithWork_cost r.lo parent.lo (sourceChild parent i).hi B
      (hhi i) (by omega) (by omega) (by have := hsource i; omega)
    have hrad := binaryNaturalMulWithWork_cost 6 b
    have hleft := naturalDistanceLeWithWork_cost
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).lo).1 (states i).lo
      (bitWordValue (binaryNaturalMulWithWork 6 b).1) B
      (by rw [translatedEndpointWithWork_value _ _ _ (hlo i)]; exact (hanchor i).1)
      (hstate i).1 (by rw [binaryNaturalMulWithWork_value]; exact hradius)
    have hright := naturalDistanceLeWithWork_cost
      (translatedEndpointWithWork r.lo parent.lo (sourceChild parent i).hi).1 (states i).hi
      (bitWordValue (binaryNaturalMulWithWork 6 b).1) B
      (by rw [translatedEndpointWithWork_value _ _ _ (hhi i)]; exact (hanchor i).2)
      (hstate i).2 (by rw [binaryNaturalMulWithWork_value]; exact hradius)
    norm_num only [show Nat.size 6 = 3 by decide] at hrad
    dsimp only
    unfold anchorGuardBitBudget
    omega
  have ha := allWithWork_cost _ (List.finRange M) (anchorGuardBitBudget B)
    (fun i _ => hanchorCost i)
  obtain ⟨htw, htc⟩ := bandToleranceWithWork_bounds tau theta b M B htau htheta hb hM
  have hc := allWithWork_cost
    (cutGuardWithWork parent r actions hne child states velocity (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) C (by
      intro j _
      exact (cutGuardWithWork_cost parent r actions hne child states velocity
        (bandToleranceWithWork tau theta b M).1 j B hvel htw hr hp (hstate j).1
        (hsource j).1 (hsource j).1 hstates hchild).trans (hC j))
  simp only [List.length_ofFn] at hconn
  simp only [List.length_finRange] at ha hc
  change _ + _ + _ + _ + 4 ≤ _
  unfold bandPredicateBitBudget
  dsimp only at ha hc ⊢
  omega

end BinaryFraction
end EditApproximation

end OAI
