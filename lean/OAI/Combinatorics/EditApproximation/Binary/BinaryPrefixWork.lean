import OAI.Combinatorics.EditApproximation.Binary.BinaryDistanceWork

namespace OAI

/-! Literal stored-fraction evaluation of the finite prefix predictor.
Every prefix minimum scans the finite action array and uses exact
Boolean comparisons. No rational operation is assigned unit cost. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

def prefixWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    BinaryFraction × ℕ :=
  let finish := canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
  let connection := connectionWithWork (nat r.lo) finish.1 ((List.ofFn states).take j)
  let total := sumListWithWork (List.ofFn fun i : Fin M =>
    if i.val < j then child i (states i) else zero)
  let result := canonicalAddWithWork connection.1 total.1
  (result.1, finish.2 + connection.2 + total.2 + result.2 +
    Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + Nat.size r.lo + 6 * M + 5)

@[simp] theorem prefixWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    (prefixWithWork parent r states child j p).1.value =
      rationalWidePrefixCost parent r states (fun i q => (child i q).value) j p.value := by
  simp only [prefixWithWork, canonicalAddWithWork_value, connectionWithWork_value,
    nat_value, sumListWithWork_value, List.map_ofFn, List.sum_ofFn, rationalWidePrefixCost]
  congr 1
  apply sum_congr rfl
  intro i _
  by_cases hi : i.val < j <;> simp [hi, zero, value, SignedBinary.value, signedMagnitude, bitWordValue]

def prefixConnectionWord (M j B : ℕ) : ℕ := connectionWordBudget (min j M) (8 * B + 6)

def prefixWordBudget (M j B : ℕ) : ℕ :=
  8 * (prefixConnectionWord M j B + bandMassTotalStorageBudget M B) + 6

def prefixBitBudget (M j B : ℕ) : ℕ :=
  6000 * (B + 1) ^ 2 + connectionBitBudget (min j M) (8 * B + 6) +
    storedSumBitBudget M B + 6 * M +
    6000 * (prefixConnectionWord M j B + bandMassTotalStorageBudget M B + 1) ^ 2 +
    2 * B + 6 * M + 5

private theorem prefix_parts {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    let finish := canonicalAddWithWork (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p
    let connection := connectionWithWork (nat r.lo) finish.1 ((List.ofFn states).take j)
    let total := sumListWithWork (List.ofFn fun i : Fin M =>
      if i.val < j then child i (states i) else zero)
    connection.1.width ≤ prefixConnectionWord M j B ∧
    total.1.width ≤ bandMassTotalStorageBudget M B ∧
    connection.2 ≤ connectionBitBudget (min j M) (8 * B + 6) ∧
    total.2 ≤ storedSumBitBudget M B + 6 * M := by
  dsimp only
  have hfinish := canonicalAddWithWork_width
    (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p B
    ((nat_width_le _).trans hcut) hp
  have hstart : (nat r.lo).width ≤ 8 * B + 6 := by
    have := (nat_width_le r.lo).trans hr
    omega
  have hend : ∀ state ∈ (List.ofFn states).take j,
      Nat.size state.lo + 2 ≤ 8 * B + 6 ∧ Nat.size state.hi + 2 ≤ 8 * B + 6 := by
    intro state hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hs)
    have hi := hstate i
    omega
  have hlist : ∀ a ∈ (List.ofFn fun i : Fin M =>
      if i.val < j then child i (states i) else zero), a.width ≤ B := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split_ifs
    · exact hchild i
    · have : zero.width = 1 := rfl
      have := hcut
      omega
  have hw := connectionWithWork_width (nat r.lo) _ ((List.ofFn states).take j)
    (8 * B + 6) hstart hfinish hend
  have hc := connectionWithWork_cost (nat r.lo) _ ((List.ofFn states).take j)
    (8 * B + 6) hstart hfinish hend
  have htw := sumListWithWork_width _ B hlist
  have htc := sumListWithWork_cost _ B hlist
  simp only [List.length_take, List.length_ofFn] at hw hc htw htc
  exact ⟨hw, htw, hc, htc⟩

theorem prefixWithWork_width {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    (prefixWithWork parent r states child j p).1.width ≤ prefixWordBudget M j B := by
  obtain ⟨hw, htw, _, _⟩ := prefix_parts parent r states child j p B hp hr hcut hstate hchild
  exact canonicalAddWithWork_width _ _ _
    (hw.trans (Nat.le_add_right _ _)) (htw.trans (Nat.le_add_left _ _))

theorem prefixWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ i, Nat.size (states i).lo + 2 ≤ B ∧ Nat.size (states i).hi + 2 ≤ B)
    (hchild : ∀ i, (child i (states i)).width ≤ B) :
    (prefixWithWork parent r states child j p).2 ≤ prefixBitBudget M j B := by
  obtain ⟨hw, htw, hc, htc⟩ := prefix_parts parent r states child j p B hp hr hcut hstate hchild
  have hf := canonicalAddWithWork_cost
    (nat (balancedCut parent.lo (parent.hi - parent.lo) M j)) p B
    ((nat_width_le _).trans hcut) hp
  have ha := canonicalAddWithWork_cost _ _
    (prefixConnectionWord M j B + bandMassTotalStorageBudget M B)
    (hw.trans (Nat.le_add_right _ _)) (htw.trans (Nat.le_add_left _ _))
  change _ + _ + _ + _ + _ + _ + 6 * M + 5 ≤ _
  unfold prefixBitBudget
  omega

def prefixMinimumWithWork {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    BinaryFraction × ℕ :=
  let fallback := prefixWithWork parent r (actions.head hne) child j p
  let scores := arithmeticMapWithWork (fun action => prefixWithWork parent r action child j p) actions
  let result := minimumWithWork fallback.1 scores.1
  (result.1, fallback.2 + scores.2 + result.2 + 1)

@[simp] theorem prefixMinimumWithWork_value {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction) :
    (prefixMinimumWithWork parent r actions hne child j p).1.value =
      rationalWidePrefixMinimum parent r actions hne (fun i q => (child i q).value) j p.value := by
  simp only [prefixMinimumWithWork, minimumWithWork_value, arithmeticMapWithWork_value,
    List.map_map, Function.comp_def, prefixWithWork_value, rationalWidePrefixMinimum]

def prefixMinimumBitBudget (M j v B : ℕ) : ℕ :=
  prefixBitBudget M j B + v * (prefixBitBudget M j B + 3) +
    (1 + v * (1000 * (prefixWordBudget M j B + 1) ^ 2 + 2)) + 1

theorem prefixMinimumWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (child : Fin M → TargetInterval ny → BinaryFraction) (j : ℕ) (p : BinaryFraction)
    (B : ℕ) (hp : p.width ≤ B) (hr : Nat.size r.lo + 2 ≤ B)
    (hcut : Nat.size (balancedCut parent.lo (parent.hi - parent.lo) M j) + 2 ≤ B)
    (hstate : ∀ action ∈ actions, ∀ i,
      Nat.size (action i).lo + 2 ≤ B ∧ Nat.size (action i).hi + 2 ≤ B)
    (hchild : ∀ action ∈ actions, ∀ i, (child i (action i)).width ≤ B) :
    (prefixMinimumWithWork parent r actions hne child j p).1.width ≤ prefixWordBudget M j B ∧
    (prefixMinimumWithWork parent r actions hne child j p).2 ≤
      prefixMinimumBitBudget M j actions.length B := by
  have hw (action) (ha : action ∈ actions) :=
    prefixWithWork_width parent r action child j p B hp hr hcut (hstate action ha) (hchild action ha)
  have hc (action) (ha : action ∈ actions) :=
    prefixWithWork_cost parent r action child j p B hp hr hcut (hstate action ha) (hchild action ha)
  have hf := List.head_mem hne
  have hmap : ∀ a ∈ (arithmeticMapWithWork
      (fun action => prefixWithWork parent r action child j p) actions).1,
      a.width ≤ prefixWordBudget M j B := by
    intro a ha
    rw [arithmeticMapWithWork_value] at ha
    obtain ⟨action, hmem, heq⟩ := List.mem_map.mp ha
    subst a
    exact hw action hmem
  have hmw := minimumWithWork_width _ _ _ (hw _ hf) hmap
  have hmc := minimumWithWork_cost _ _ _ (hw _ hf) hmap
  have hsc := arithmeticMapWithWork_cost
    (fun action => prefixWithWork parent r action child j p) actions (prefixBitBudget M j B) hc
  have hlen : (arithmeticMapWithWork
      (fun action => prefixWithWork parent r action child j p) actions).1.length = actions.length := by
    rw [arithmeticMapWithWork_value, List.length_map]
  rw [hlen] at hmc
  refine ⟨hmw, ?_⟩
  have hfc := hc _ hf
  change _ + _ + _ + 1 ≤ _
  unfold prefixMinimumBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
