import Mathlib

namespace OAI


namespace Problem355.Digits

theorem take_eq_of_ofDigits_mod_eq {b j : ℕ} (hb : 1 < b)
    {A B : List ℕ} (hlen : A.length = B.length)
    (hA : ∀ a ∈ A, a < b) (hB : ∀ a ∈ B, a < b)
    (hmod : Nat.ofDigits b A % b ^ j = Nat.ofDigits b B % b ^ j) :
    A.take j = B.take j := by
  apply Nat.ofDigits_inj_of_len_eq hb
  · simp [hlen]
  · exact fun a ha => hA a (List.mem_of_mem_take ha)
  · exact fun a ha => hB a (List.mem_of_mem_take ha)
  · simpa only [Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) A hA,
      Nat.ofDigits_mod_pow_eq_ofDigits_take j (by omega) B hB] using hmod

theorem ofDigits_ofFn_eq_sum (b : ℕ) {k : ℕ} (d : Fin k → ℕ) :
    Nat.ofDigits b (List.ofFn d) = ∑ i : Fin k, d i * b ^ i.val := by
  simp [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
    List.length_ofFn, Fin.val_cast, List.sum_ofFn]

theorem initial_digits_eq_of_sum_mod_eq {b k j : ℕ} (hb : 1 < b)
    {d e : Fin k → ℕ} (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
    (hmod : (∑ i : Fin k, d i * b ^ i.val) % b ^ j =
      (∑ i : Fin k, e i * b ^ i.val) % b ^ j) :
    ∀ i : Fin k, i.val < j → d i = e i := by
  have htake : (List.ofFn d).take j = (List.ofFn e).take j := by
    apply take_eq_of_ofDigits_mod_eq hb (by simp)
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hd i
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact he i
    · simpa only [ofDigits_ofFn_eq_sum] using hmod
  intro i hi
  have hget := congrArg (fun l : List ℕ => l[i.val]?) htake
  simpa [List.getElem?_take, hi] using hget

theorem card_residue_fiber_le {X : Type*} [Fintype X]
    {b j k : ℕ} (hb : 1 < b)
    (digit : Fin (j + k) → X → Fin b)
    (hinj : ∀ i, Function.Injective (digit i)) (r : ℕ) :
    (Finset.univ.filter (fun x : Fin (j + k) → X =>
      (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j = r)).card
      ≤ Fintype.card X ^ k := by
  classical
  let tail : (Fin (j + k) → X) → (Fin k → X) :=
    fun x i => x (Fin.natAdd j i)
  have hcard := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun x : Fin (j + k) → X =>
      (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j = r))
    (t := Finset.univ) tail (by intro x hx; exact Finset.mem_univ _)
  have htail : Set.InjOn tail
      ↑(Finset.univ.filter (fun x : Fin (j + k) → X =>
        (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j = r)) := by
    intro x hx y hy hxy
    have hmod :
        (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j =
        (∑ i : Fin (j + k), (digit i (y i)).val * b ^ i.val) % b ^ j :=
      (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    have hfirst := initial_digits_eq_of_sum_mod_eq hb
      (fun i => (digit i (x i)).isLt) (fun i => (digit i (y i)).isLt) hmod
    funext i
    refine Fin.addCases (fun u => ?_) (fun v => ?_) i
    · apply hinj (Fin.castAdd k u)
      apply Fin.ext
      exact hfirst (Fin.castAdd k u) u.isLt
    · exact congrFun hxy v
  simpa using hcard htail

theorem card_residue_fiber_mul_le {X : Type*} [Fintype X]
    {b j k : ℕ} (hb : 1 < b)
    (digit : Fin (j + k) → X → Fin b)
    (hinj : ∀ i, Function.Injective (digit i)) (r : ℕ) :
    (Finset.univ.filter (fun x : Fin (j + k) → X =>
      (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j = r)).card *
        Fintype.card X ^ j ≤ Fintype.card X ^ (j + k) := by
  classical
  calc
    _ ≤ Fintype.card X ^ k * Fintype.card X ^ j :=
      Nat.mul_le_mul_right _ (card_residue_fiber_le hb digit hinj r)
    _ = _ := by rw [← pow_add, Nat.add_comm k j]

theorem residue_fiber_fraction_le {X : Type*} [Fintype X]
    {b j k : ℕ} (hb : 1 < b) (hX : 0 < Fintype.card X)
    (digit : Fin (j + k) → X → Fin b)
    (hinj : ∀ i, Function.Injective (digit i)) (r : ℕ) :
    ((Finset.univ.filter (fun x : Fin (j + k) → X =>
      (∑ i : Fin (j + k), (digit i (x i)).val * b ^ i.val) % b ^ j = r)).card : ℝ) /
        (Fintype.card X : ℝ) ^ (j + k) ≤ 1 / (Fintype.card X : ℝ) ^ j := by
  classical
  have hX' : (0 : ℝ) < Fintype.card X := by exact_mod_cast hX
  apply (div_le_div_iff₀ (pow_pos hX' _) (pow_pos hX' _)).2
  simp only [one_mul]
  exact_mod_cast card_residue_fiber_mul_le hb digit hinj r

end Problem355.Digits

end OAI
