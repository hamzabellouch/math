import OAI.Computability.WLIdentification.MateReconstruction

namespace OAI

namespace WLIdentification

namespace CycleRows

open scoped BigOperators

/-- The rectangular difference of a vanishing cycle sum isolates one edge.
No finiteness or cardinality assumption on the coordinate alphabets is needed. -/
theorem rectangle {I : Type} [Fintype I] [DecidableEq I]
    (s : Equiv.Perm I) (hs : ∀ i, s i ≠ i) (hs2 : ∀ i, s (s i) ≠ i)
    (A : I → Type) (g : (i : I) → A i → A (s i) → Bit)
    (hzero : ∀ a : (i : I) → A i, ∑ i, g i (a i) (a (s i)) = 0)
    (b : (i : I) → A i) (i : I) (u : A i) (v : A (s i)) :
    g i u v + g i u (b (s i)) + g i (b i) v + g i (b i) (b (s i)) = 0 := by
  let bu := Function.update b i u
  let bv := Function.update b (s i) v
  let buv := Function.update bu (s i) v
  let d (j : I) := g j (buv j) (buv (s j)) + g j (bu j) (bu (s j)) +
    g j (bv j) (bv (s j)) + g j (b j) (b (s j))
  have hd (j : I) (hj : j ≠ i) : d j = 0 := by
    by_cases hj' : j = s i
    · subst j
      have hnext : s (s i) ≠ s i := s.injective.ne (hs i)
      dsimp only [d, buv, bu, bv]
      simp only [Function.update_self, Function.update_of_ne (hs i),
        Function.update_of_ne (hs2 i), Function.update_of_ne hnext]
      rw [add_assoc, CharTwo.add_self_eq_zero]
    · have hnext : s j ≠ s i := s.injective.ne hj
      dsimp only [d, buv, bv]
      simp only [Function.update_of_ne hj', Function.update_of_ne hnext]
      rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  have hsum : ∑ j, d j = 0 := by
    simp only [d, Finset.sum_add_distrib, hzero, add_zero]
  have hdi : d i = 0 := by
    rw [Finset.sum_eq_single i (fun j _ hj => hd j hj) (fun h => (h (Finset.mem_univ i)).elim)] at hsum
    exact hsum
  have hi : i ≠ s i := (hs i).symm
  simpa only [d, buv, bu, bv, Function.update_self, Function.update_of_ne hi,
    Function.update_of_ne (hs i)] using hdi

/-- Varying a single coordinate equates the two adjacent one-coordinate deviations. -/
theorem adjacent_deviation {I : Type} [Fintype I] [DecidableEq I]
    (s : Equiv.Perm I) (hs : ∀ i, s i ≠ i)
    (A : I → Type) (g : (i : I) → A i → A (s i) → Bit)
    (hzero : ∀ a : (i : I) → A i, ∑ i, g i (a i) (a (s i)) = 0)
    (b : (i : I) → A i) (i : I) (v : A (s i)) :
    g i (b i) v + g i (b i) (b (s i)) =
      g (s i) v (b (s (s i))) + g (s i) (b (s i)) (b (s (s i))) := by
  let bv := Function.update b (s i) v
  let d (j : I) := g j (bv j) (bv (s j)) + g j (b j) (b (s j))
  have hd (j : I) (hj : j ≠ i) (hj' : j ≠ s i) : d j = 0 := by
    dsimp only [d, bv]
    simp only [Function.update_of_ne hj', Function.update_of_ne (s.injective.ne hj),
      CharTwo.add_self_eq_zero]
  have hsum : ∑ j, d j = 0 := by
    simp only [d, Finset.sum_add_distrib, hzero, zero_add]
  have hp : ∑ j ∈ {i, s i}, d j = ∑ j, d j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact hd j hj.1 hj.2
  rw [Finset.sum_pair (hs i).symm, hsum] at hp
  have hi : i ≠ s i := (hs i).symm
  have hnext : s (s i) ≠ s i := s.injective.ne (hs i)
  simpa only [d, bv, Function.update_self, Function.update_of_ne hi,
    Function.update_of_ne hnext] using CharTwo.add_eq_zero.mp hp

theorem rotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    by_cases hi : i.val < n
    · have hh : i = ⟨i.val, i.isLt⟩ := rfl
      rw [hh, finRotate_of_lt hi]
      simp only [ite_eq_left (by omega : i.val + 1 < n + 1)]
    · have hi' : i = Fin.last n := by
        apply Fin.ext
        change i.val = n
        have := i.isLt
        omega
      rw [hi', finRotate_last]
      simp

theorem rotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hw := rotate_val i
  rw [h] at hw
  split_ifs at hw <;> omega

theorem rotate_twice_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro h
  have hw := rotate_val i
  have hw' := rotate_val (finRotate n i)
  rw [h] at hw'
  split_ifs at hw hw' <;> omega

/-- Integrating constants around a finite cycle needs exactly the zero-sum condition. -/
theorem integrate_constants {n : ℕ} (c : Fin n → Bit) (hc : ∑ i, c i = 0) :
    ∃ C : Fin n → Bit, ∀ i, C i + C (finRotate n i) = c i := by
  let f (j : ℕ) : Bit := if h : j < n then c ⟨j, h⟩ else 0
  let C (i : Fin n) : Bit := ∑ j ∈ Finset.range i.val, f j
  have hf (i : Fin n) : f i.val = c i := by simp [f, i.isLt]
  have htotal : ∑ j ∈ Finset.range n, f j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [hf] using hc
  refine ⟨C, ?_⟩
  intro i
  have hn := i.isLt
  have hi := rotate_val i
  by_cases hlt : i.val + 1 < n
  · rw [ite_eq_left hlt] at hi
    change C i + (∑ j ∈ Finset.range (finRotate n i).val, f j) = c i
    rw [hi, Finset.sum_range_succ, hf]
    change C i + (C i + c i) = c i
    exact CharTwo.add_cancel_left _ _
  · rw [ite_eq_right hlt] at hi
    have hn' : n = i.val + 1 := by omega
    rw [hn', Finset.sum_range_succ, hf] at htotal
    have hci : C i = c i := CharTwo.add_eq_zero.mp htotal
    change C i + (∑ j ∈ Finset.range (finRotate n i).val, f j) = c i
    rw [hi, Finset.range_zero, Finset.sum_empty, add_zero, hci]

theorem cycle_lifting {r : ℕ} (hr : 3 ≤ r) (A : Fin r → Type)
    (g : (i : Fin r) → A i → A (finRotate r i) → Bit)
    (b : (i : Fin r) → A i)
    (hzero : ∀ a : (i : Fin r) → A i, ∑ i, g i (a i) (a (finRotate r i)) = 0) :
    ∃ Y : (i : Fin r) → A i → Bit,
      ∀ i u v, g i u v = Y i u + Y (finRotate r i) v := by
  let s := finRotate r
  let c (i : Fin r) : Bit := g i (b i) (b (s i))
  let alpha (i : Fin r) (u : A i) : Bit := g i u (b (s i)) + c i
  obtain ⟨C, hC⟩ := integrate_constants c (hzero b)
  refine ⟨fun i u => alpha i u + C i, ?_⟩
  intro i u v
  have hs := fun j => rotate_ne_self (by omega : 2 ≤ r) j
  have hrect := rectangle s hs (rotate_twice_ne_self hr) A g hzero b i u v
  have hdev := adjacent_deviation s hs A g hzero b i v
  have hsep : g i u v = g i u (b (s i)) + g i (b i) v + c i := by
    apply CharTwo.add_eq_zero.mp
    simpa only [c, add_assoc] using hrect
  have hdev' : alpha (s i) v = g i (b i) v + c i := hdev.symm
  have hcc : C i + C (s i) = c i := hC i
  apply Eq.symm
  calc
    (alpha i u + C i) + (alpha (s i) v + C (s i)) =
        (g i u (b (s i)) + g i (b i) v) + (c i + c i) + (C i + C (s i)) := by
      rw [hdev']
      dsimp only [alpha]
      abel
    _ = g i u (b (s i)) + g i (b i) v + c i := by
      rw [CharTwo.add_self_eq_zero, add_zero, hcc]
    _ = g i u v := hsep.symm

end CycleRows

end WLIdentification

end OAI
