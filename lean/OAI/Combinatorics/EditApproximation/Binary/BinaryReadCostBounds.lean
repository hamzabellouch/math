import OAI.Combinatorics.EditApproximation.Binary.BinaryOnlineReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryScoreReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGrid

namespace OAI

/-! Lookup overhead is controlled by the loops that actually run.
These comparisons require only a bound on one finite-buffer lookup. -/

namespace EditApproximation

theorem vectorMapWithWork_cost_lower {α : Type*} (d : ℕ) (f : Fin d → α × ℕ) (C : ℕ)
    (h : ∀ i, C ≤ (f i).2) : d * C ≤ (vectorMapWithWork d f).2 := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  omega

theorem arithmeticMapWithWork_factor {α β : Type*} (read plain : α → β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
    (arithmeticMapWithWork read xs).2 ≤ (arithmeticMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticMapWithWork, hx, ht.1]
    · simp only [arithmeticMapWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem vectorMapWithWork_factor {α : Type*} (d : ℕ) (read plain : Fin d → α × ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hv : ∀ i, (read i).1 = (plain i).1)
    (hc : ∀ i, (read i).2 ≤ (plain i).2 * K) :
    (vectorMapWithWork d read).1 = (vectorMapWithWork d plain).1 ∧
    (vectorMapWithWork d read).2 ≤ (vectorMapWithWork d plain).2 * K := by
  constructor
  · apply Vector.ext
    intro i hi
    change (vectorMapWithWork d read).1.get ⟨i, hi⟩ = (vectorMapWithWork d plain).1.get ⟨i, hi⟩
    rw [vectorMapWithWork_value, vectorMapWithWork_value]
    exact hv _
  · simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
    rw [← Finset.sum_mul] at hs
    have hd := Nat.mul_le_mul_left (6 * d) hK
    simp only [Nat.mul_one] at hd
    nlinarith only [hs, hd]


theorem filterWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
    (filterWithWork read xs).2 ≤ (filterWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [filterWithWork, hx, ht.1]
    · simp only [filterWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem allWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
    (allWithWork read xs).2 ≤ (allWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [allWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [allWithWork, hx, ht.1]
    · simp only [allWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem filterMapWithWork_factor {α β : Type*} (read plain : α → Option β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterMapWithWork read xs).1 = (filterMapWithWork plain xs).1 ∧
    (filterMapWithWork read xs).2 ≤ (filterMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [filterMapWithWork, hx, ht.1]
    cases (plain x).1 with
    | none => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩
    | some value => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩

/-- Multiplicative work bounds are preserved when the same nonnegative
overhead is added to both counters. -/
theorem cost_replace_factor (a c old new K : ℕ) (hc : c ≤ a * K) (hK : 1 ≤ K)
    (ha : a ≤ old) (hn : new + a ≤ old + c) : new ≤ old * K := by
  have hx := Nat.mul_le_mul_left (old - a) hK
  simp only [Nat.mul_one] at hx
  have he : a + (old - a) = old := by omega
  calc
    new ≤ c + (old - a) := by omega
    _ ≤ a * K + (old - a) * K := Nat.add_le_add hc hx
    _ = old * K := by rw [← Nat.add_mul, he]

/-- A compulsory constant instruction pays for one additional lookup. -/
theorem cost_factor_with_read (a c x r R K : ℕ) (hc : c ≤ a * K)
    (hr : r ≤ R) (hx : 1 ≤ x) (hK : R + 1 ≤ K) :
    r + c + x ≤ (a + x) * K := by
  have hmul := Nat.mul_le_mul_left x hK
  have hR := Nat.mul_le_mul_right R hx
  simp only [Nat.one_mul] at hR
  have hrest : r + x ≤ x * K := by nlinarith only [hmul, hR, hr]
  calc
    r + c + x = c + (r + x) := by omega
    _ ≤ a * K + x * K := Nat.add_le_add hc hrest
    _ = (a + x) * K := by ring

namespace BinaryFraction

def tableReadFactor (R : ℕ) : ℕ := 4 * (R + 4)

theorem tableReadFactor_pos (R : ℕ) : 1 ≤ tableReadFactor R := by
  unfold tableReadFactor
  omega

theorem tableReadFactor_absorb (a c n R : ℕ) (hc : c ≤ a + n * (R + 3)) (hn : n ≤ a) :
    c ≤ a * tableReadFactor R := by
  have hm := Nat.mul_le_mul_right (R + 3) hn
  have hk : R + 4 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    c ≤ a + a * (R + 3) := hc.trans (Nat.add_le_add_left hm a)
    _ = a * (R + 4) := by ring
    _ ≤ a * tableReadFactor R := Nat.mul_le_mul_left a hk

theorem endpointScoreReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ M R (endpointScoreReadWithWork_cost r read states R hr)
  simp only [endpointScoreWithWork, endpointConnectionWithWork]
  omega

theorem prefixReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx) (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * tableReadFactor R := by
  have hc := prefixReadWithWork_cost parent r states read j p R hr
  have hn : M ≤ (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 := by
    simp only [prefixWithWork]
    omega
  have hm := Nat.mul_le_mul_right (R + 4) hn
  have hk : R + 5 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    _ ≤ _ + M * (R + 4) := hc
    _ ≤ _ + (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 4) :=
      Nat.add_le_add_left hm _
    _ = (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 5) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hk

theorem bandEnvelopeReadWithWork_factor {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) (R : ℕ)
    (hr : ∀ action ∈ band, (read i (action i)).2 ≤ R) :
    (bandEnvelopeReadWithWork b band read i).2 ≤
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ band.length R (bandEnvelopeReadWithWork_cost b band read i R hr)
  simp only [bandEnvelopeWithWork]
  omega

theorem onlineLinearReadWithWork_factor {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 * tableReadFactor R := by
  have hc := (onlineLinearReadWithWork_eq_cost mass read eta kappa t i R hr).2
  have ht : 6 * t ≤ (vectorMapWithWork t (fun s => optimisticTermWithWork mass
      (fun v j => (read v j).1) (coefficientWithWork kappa).1 s.val i)).2 := by
    simp only [vectorMapWithWork]
    omega
  have hn : 3 * t + 1 ≤ (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 := by
    simp only [onlineLinearWithWork, gainWithWork]
    omega
  apply tableReadFactor_absorb _ _ (3 * t + 1) R _ hn
  exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : R ≤ R + 3)) _)

end BinaryFraction
end EditApproximation

end OAI
