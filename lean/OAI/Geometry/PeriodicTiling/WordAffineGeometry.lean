import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int

namespace OAI

namespace PeriodicTilingThree

def FourLineClosure (N : ℤ) (Good : ℤ → ℤ → Prop) : Prop :=
  ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
    ∀ r : ℤ, 0 ≤ r → r + 3 < N →
      (∀ i : Fin 4, Good (r + i.val) (d * (r + i.val) + e)) →
      ∀ n : ℤ, 0 ≤ n → n < N → Good n (d * n + e)

def FourGoodRows (N : ℤ) (Good : ℤ → ℤ → Prop) (q : ℤ) : Prop :=
  ∀ m : ℤ, q ≤ m → m ≤ q + 3 →
    ∀ n : ℤ, 0 ≤ n → n < N → Good n m

theorem fourGoodRows_row_above (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    ∀ n : ℤ, 0 ≤ n → n < N → Good n (q + 4) := by
  intro n hn0 hnN
  by_cases hr : n + 4 < N
  · have hseed : ∀ i : Fin 4,
        Good (n + 1 + i.val) ((-1) * (n + 1 + i.val) + (n + q + 4)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + 3 - i.val) (by omega) (by omega)
        (n + 1 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [neg_one_mul]; omega
    have h := hline (-1) (n + q + 4) (Or.inl rfl)
      (n + 1) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [neg_one_mul]; omega
  · have hl : 4 ≤ n := by omega
    have hseed : ∀ i : Fin 4,
        Good (n - 4 + i.val) (1 * (n - 4 + i.val) + (q + 4 - n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + i.val) (by omega) (by omega)
        (n - 4 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [one_mul]; omega
    have h := hline 1 (q + 4 - n) (Or.inr (Or.inr rfl))
      (n - 4) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [one_mul]; omega

theorem fourGoodRows_row_below (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    ∀ n : ℤ, 0 ≤ n → n < N → Good n (q - 1) := by
  intro n hn0 hnN
  by_cases hr : n + 4 < N
  · have hseed : ∀ i : Fin 4,
        Good (n + 1 + i.val) (1 * (n + 1 + i.val) + (q - 1 - n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + i.val) (by omega) (by omega)
        (n + 1 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [one_mul]; omega
    have h := hline 1 (q - 1 - n) (Or.inr (Or.inr rfl))
      (n + 1) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [one_mul]; omega
  · have hl : 4 ≤ n := by omega
    have hseed : ∀ i : Fin 4,
        Good (n - 4 + i.val) ((-1) * (n - 4 + i.val) + (q - 1 + n)) := by
      intro i
      have hi : 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) < 4 := by omega
      have hg := hrows (q + 3 - i.val) (by omega) (by omega)
        (n - 4 + i.val) (by omega) (by omega)
      convert hg using 1; simp only [neg_one_mul]; omega
    have h := hline (-1) (q - 1 + n) (Or.inl rfl)
      (n - 4) (by omega) (by omega) hseed n hn0 hnN
    convert h using 1; simp only [neg_one_mul]; omega

theorem fourGoodRows_add_one (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    FourGoodRows N Good (q + 1) := by
  intro m hm0 hm3 n hn0 hnN
  by_cases hm : m ≤ q + 3
  · exact hrows m (by omega) hm n hn0 hnN
  · have he : m = q + 4 := by omega
    rw [he]
    exact fourGoodRows_row_above N hN Good hline q hrows n hn0 hnN

theorem fourGoodRows_sub_one (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (q : ℤ) (hrows : FourGoodRows N Good q) :
    FourGoodRows N Good (q - 1) := by
  intro m hm0 hm3 n hn0 hnN
  by_cases hm : q ≤ m
  · exact hrows m hm (by omega) n hn0 hnN
  · have he : m = q - 1 := by omega
    rw [he]
    exact fourGoodRows_row_below N hN Good hline q hrows n hn0 hnN

theorem good_everywhere_of_four_square (N : ℤ) (hN : 8 ≤ N)
    (Good : ℤ → ℤ → Prop) (hline : FourLineClosure N Good)
    (r q : ℤ) (hr0 : 0 ≤ r) (hr3 : r + 3 < N)
    (hsquare : ∀ i j : Fin 4, Good (r + i.val) (q + j.val)) :
    ∀ n m : ℤ, 0 ≤ n → n < N → Good n m := by
  have hbase : FourGoodRows N Good q := by
    intro m hm0 hm3 n hn0 hnN
    let j : Fin 4 := ⟨(m - q).toNat, by omega⟩
    have hj : q + (j.val : ℤ) = m := by dsimp [j]; omega
    have hseed : ∀ i : Fin 4, Good (r + i.val) (0 * (r + i.val) + m) := by
      intro i
      simpa only [zero_mul, zero_add, hj] using hsquare i j
    have h := hline 0 m (Or.inr (Or.inl rfl)) r hr0 hr3 hseed n hn0 hnN
    simpa only [zero_mul, zero_add] using h
  have hall : ∀ t : ℤ, FourGoodRows N Good t := by
    intro t
    exact Int.inductionOn' t q hbase
      (fun k _ hk => fourGoodRows_add_one N hN Good hline k hk)
      (fun k _ hk => fourGoodRows_sub_one N hN Good hline k hk)
  intro n m hn0 hnN
  exact hall m m le_rfl (by omega) n hn0 hnN

end PeriodicTilingThree

end OAI
