import Mathlib
import OAI.Combinatorics.UniformKServer.DyadicRows
import OAI.Combinatorics.UniformKServer.BitPaths

namespace OAI

namespace UniformKServer.ExecutableDyadic

def numerators {k : ℕ} (q : Fin k → ℚ) (j₀ : Fin k) (B : ℕ) (j : Fin k) : ℕ :=
  if j = j₀ then B - ∑ i ∈ Finset.univ.erase j₀, ⌊(B : ℚ) * q i⌋₊
  else ⌊(B : ℚ) * q j⌋₊

def rationalCost {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ) : S → List R → ℚ
  | _, [] => 0
  | s, r::w => ∑ j, q s r j * (charge s r j + rationalCost q next charge (next s r j) w)

theorem natFloor_cast (x : ℚ) : ⌊(x : ℝ)⌋₊ = ⌊x⌋₊ := by
  rw [← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]

theorem numerators_repr {k : ℕ} (q : Fin k → ℚ) (hq : ∀ j, 0 ≤ q j)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) (j : Fin k) :
    (numerators q j₀ B j : ℝ) / B = roundedRow (fun i => (q i : ℝ)) j₀ B j := by
  classical
  have hf (i : Fin k) : ⌊(B : ℝ) * (q i : ℝ)⌋₊ = ⌊(B : ℚ) * q i⌋₊ := by
    simpa using natFloor_cast ((B : ℚ) * q i)
  have hqr (i : Fin k) : (0 : ℝ) ≤ q i := by exact_mod_cast hq i
  have hsr : ∑ i, (q i : ℝ) = 1 := by exact_mod_cast hs
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hS : ∑ i ∈ Finset.univ.erase j₀, ⌊(B : ℚ) * q i⌋₊ ≤ B := by
    have hn := round_row_nonneg (fun i => (q i : ℝ)) hqr hsr j₀ B hB j₀
    simp only [roundedRow, ↓reduceIte, hf, ← Finset.sum_div] at hn
    have hr : (∑ i ∈ Finset.univ.erase j₀, (⌊(B : ℚ) * q i⌋₊ : ℝ)) ≤ B :=
      (div_le_one hb).mp (by linarith)
    exact_mod_cast hr
  by_cases hj : j = j₀
  · subst j
    simp only [numerators, roundedRow, ↓reduceIte, Nat.cast_sub hS, Nat.cast_sum, hf]
    rw [sub_div, div_self (ne_of_gt hb), Finset.sum_div]
  · simp [numerators, roundedRow, hj, hf]

theorem numerators_sum {k : ℕ} (q : Fin k → ℚ) (hq : ∀ j, 0 ≤ q j)
    (hs : ∑ j, q j = 1) (j₀ : Fin k) (B : ℕ) (hB : 0 < B) :
    ∑ j, numerators q j₀ B j = B := by
  have ht := round_row_sum (fun i => (q i : ℝ)) j₀ B
  simp only [← numerators_repr q hq hs j₀ B hB, ← Finset.sum_div] at ht
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have heq := (div_eq_one_iff_eq hb).mp ht
  exact_mod_cast heq

theorem rationalCost_cast {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (s : S) (r : R) (w : List R) :
    (rationalCost q next charge s (r::w) : ℝ) =
      ∑ j, (q s r j : ℝ) * ((charge s r j : ℝ) +
        (rationalCost q next charge (next s r j) w : ℝ)) := by
  simp only [rationalCost, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]

theorem rationalCost_bounds {S R : Type*} {k : ℕ} (q : S → R → Fin k → ℚ)
    (hq : ∀ s r j, 0 ≤ q s r j) (hs : ∀ s r, ∑ j, q s r j = 1)
    (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) (s : S) (w : List R) :
    0 ≤ (rationalCost q next charge s w : ℝ) ∧
      (rationalCost q next charge s w : ℝ) ≤ w.length * D := by
  induction w generalizing s with
  | nil => simp [rationalCost]
  | cons r w ih =>
    rw [rationalCost_cast]
    have hqr (j : Fin k) : (0 : ℝ) ≤ q s r j := by exact_mod_cast hq s r j
    have hnr (j : Fin k) : (0 : ℝ) ≤ charge s r j := by exact_mod_cast hn s r j
    have hsr : ∑ j, (q s r j : ℝ) = 1 := by exact_mod_cast hs s r
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hqr j)
        (add_nonneg (hnr j) (ih (next s r j)).1))
    · calc
        _ ≤ ∑ j, (q s r j : ℝ) * (((w.length : ℝ) + 1) * D) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hqr j)
          have := hd s r j
          have := (ih (next s r j)).2
          nlinarith
        _ = _ := by rw [← Finset.sum_mul, hsr]; simp

theorem rowCost_bound {S R : Type*} {k : ℕ}
    (q : S → R → Fin k → ℚ) (hq : ∀ s r j, 0 ≤ q s r j)
    (hs : ∀ s r, ∑ j, q s r j = 1) (reserve : S → R → Fin k)
    (b : ℕ) (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) (s : S) (w : List R) :
    BitSampling.rowCost (b:=b) (fun s r => numerators (q s r) (reserve s r) (2^b))
      next (fun s r j => (charge s r j : ℝ)) s w ≤
        (rationalCost q next charge s w : ℝ) +
          (k : ℝ) * (w.length : ℝ)^2 / ((2^b : ℕ) : ℝ) * D := by
  let N := fun s r => numerators (q s r) (reserve s r) (2^b)
  have hB : 0 < 2^b := by positivity
  have hb : (0 : ℝ) < (2^b : ℕ) := by exact_mod_cast hB
  have hqr (s : S) (r : R) (j : Fin k) : (0 : ℝ) ≤ q s r j := by
    exact_mod_cast hq s r j
  have hsr (s : S) (r : R) : ∑ j, (q s r j : ℝ) = 1 := by
    exact_mod_cast hs s r
  have hrepr (s : S) (r : R) (j : Fin k) : (N s r j : ℝ) / (2^b : ℕ) =
      roundedRow (fun j => (q s r j : ℝ)) (reserve s r) (2^b) j :=
    numerators_repr (q s r) (hq s r) (hs s r) (reserve s r) (2^b) hB j
  have hnt (s : S) (r : R) : ∑ j, (N s r j : ℝ) / (2^b : ℕ) = 1 := by
    simp only [hrepr, round_row_sum]
  have hnn (s : S) (r : R) (j : Fin k) : (0 : ℝ) ≤ (N s r j : ℝ) / (2^b : ℕ) :=
    div_nonneg (Nat.cast_nonneg _) hb.le
  change BitSampling.rowCost (b:=b) N next _ s w ≤ _
  induction w generalizing s with
  | nil => simp [BitSampling.rowCost, rationalCost]
  | cons r w ih =>
    let v : Fin k → ℝ := fun j => (charge s r j : ℝ) +
      (rationalCost q next charge (next s r j) w : ℝ)
    let err : ℝ := (k : ℝ) * (w.length : ℝ)^2 / (2^b : ℕ) * D
    have hv (j : Fin k) : 0 ≤ v j ∧ v j ≤ ((w.length : ℝ) + 1) * D := by
      have hl := rationalCost_bounds q hq hs next charge hn D hd (next s r j) w
      have hn' : (0 : ℝ) ≤ charge s r j := by exact_mod_cast hn s r j
      have hu := hd s r j
      dsimp [v]
      constructor <;> nlinarith [hl.1, hl.2]
    have next_le : BitSampling.rowCost (b:=b) N next (fun s r j => (charge s r j : ℝ))
        s (r::w) ≤ (∑ j, (N s r j : ℝ) / (2^b : ℕ) * v j) + err := by
      rw [BitSampling.rowCost]
      calc
        _ ≤ ∑ j, (N s r j : ℝ) / (2^b : ℕ) * (v j + err) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hnn s r j)
          have ht := ih (next s r j)
          dsimp [v, err]
          linarith
        _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hnt, one_mul]
    have local_le := round_row_expectation (fun j => (q s r j : ℝ)) (hqr s r)
      (hsr s r) (reserve s r) (2^b) hB v (((w.length : ℝ) + 1) * D) hv
    simp only [← hrepr s r] at local_le
    have combo : BitSampling.rowCost (b:=b) N next (fun s r j => (charge s r j : ℝ))
        s (r::w) ≤ (rationalCost q next charge s (r::w) : ℝ) +
          k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) + err := by
      rw [rationalCost_cast]
      change BitSampling.rowCost (b:=b) N next _ s (r::w) ≤
        (∑ j, (q s r j : ℝ) * v j) + _ + err
      linarith
    have heps : 0 ≤ (k : ℝ) / (2^b : ℕ) * D :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hb.le) hD
    have hm : 0 ≤ (w.length : ℝ) := Nat.cast_nonneg _
    have inc : k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) + err ≤
        (k : ℝ) * ((r :: w).length : ℝ)^2 / (2^b : ℕ) * D := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, err]
      have hp := mul_nonneg heps hm
      calc
        _ ≤ k / ((2^b : ℕ) : ℝ) * (((w.length : ℝ) + 1) * D) +
            (k : ℝ) * (w.length : ℝ)^2 / (2^b : ℕ) * D +
            k / ((2^b : ℕ) : ℝ) * D * (w.length : ℝ) := le_add_of_nonneg_right hp
        _ = _ := by ring
    exact combo.trans (by linarith)

/-- Exact executable downward rounding and finite-bit realization, with the
source's full-horizon error bound; every history/state is included. -/
theorem finite_bit_perturbation {S R : Type*} {k : ℕ}
    (q : S → R → Fin k → ℚ) (hq : ∀ s r j, 0 ≤ q s r j)
    (hs : ∀ s r, ∑ j, q s r j = 1) (reserve : S → R → Fin k)
    (b : ℕ) (next : S → R → Fin k → S) (charge : S → R → Fin k → ℚ)
    (hn : ∀ s r j, 0 ≤ charge s r j) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s r j, (charge s r j : ℝ) ≤ D) :
    ∃ hN : ∀ s r, ∑ j, numerators (q s r) (reserve s r) (2^b) j = 2^b,
      (∀ s r j, j ≠ reserve s r → q s r j = 0 →
        numerators (q s r) (reserve s r) (2^b) j = 0) ∧
      (∀ s w, BitSampling.mean
        (BitSampling.runCost (fun s r => numerators (q s r) (reserve s r) (2^b))
          hN next (fun s r j => (charge s r j : ℝ)) s w) ≤
        (rationalCost q next charge s w : ℝ) +
          (k : ℝ) * (w.length : ℝ)^2 / ((2^b : ℕ) : ℝ) * D) := by
  have hN (s : S) (r : R) := numerators_sum (q s r) (hq s r) (hs s r)
    (reserve s r) (2^b) (by positivity)
  refine ⟨hN, ?_, ?_⟩
  · intro s r j hj hz
    simp [numerators, hj, hz]
  · intro s w
    rw [BitSampling.bit_path_mean]
    exact rowCost_bound q hq hs reserve b next charge hn D hD hd s w
end UniformKServer.ExecutableDyadic



end OAI
