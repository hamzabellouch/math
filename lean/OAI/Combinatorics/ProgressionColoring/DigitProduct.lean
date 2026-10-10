import OAI.Combinatorics.ProgressionColoring.Basic
import OAI.Combinatorics.ProgressionColoring.CyclicBasic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log

namespace OAI

/-!
# The digit-product transfer

For a cyclic avoiding coloring modulo `N`, color an integer by the colors of
its first `m` base-`N` digits. The first nonzero digit of a positive common
difference supplies a nonzero cyclic step. The arithmetic proof uses finite
divisibility, so it applies to composite bases as well as prime bases.

The explicit avoiding-coloring theorems are unconditional. Statements about
`W` consume the genuine finite Ramsey witness, supplied by `UpperBound` at
the final assembly; finiteness is not built into the definition of `W`.
-/

universe uAlpha

namespace QuantitativeVanDerWaerden

/-- Select the last dividing base power below a positive difference bound.
No primality assumption is needed. -/
theorem exists_base_factor {N d m : ℕ} (hd : 0 < d) (hbound : d < N ^ m) :
    ∃ i < m, ∃ e, d = N ^ i * e ∧ ¬ N ∣ e := by
  have hnot : ¬ N ^ m ∣ d := by
    intro h
    exact (not_le_of_gt hbound) (Nat.le_of_dvd hd h)
  let hex : ∃ t : ℕ, ¬ N ^ t ∣ d := ⟨m, hnot⟩
  have ht_le : Nat.find hex ≤ m := Nat.find_min' hex hnot
  have ht_pos : 0 < Nat.find hex := by
    by_contra h
    have ht_zero : Nat.find hex = 0 := by omega
    have hdvd : N ^ Nat.find hex ∣ d := by rw [ht_zero]; simp
    exact Nat.find_spec hex hdvd
  let i := Nat.find hex - 1
  have hi : i < Nat.find hex := by dsimp [i]; omega
  have hi_succ : i + 1 = Nat.find hex := by dsimp [i]; omega
  have hdiv : N ^ i ∣ d := by
    by_contra h
    exact Nat.find_min hex hi h
  obtain ⟨e, he⟩ := hdiv
  refine ⟨i, by omega, e, he, ?_⟩
  rintro ⟨q, hq⟩
  apply Nat.find_spec hex
  refine ⟨q, ?_⟩
  rw [← hi_succ, pow_succ, he, hq]
  exact (Nat.mul_assoc (N ^ i) N q).symm

/-- Exact quotient arithmetic at a coordinate whose base power divides the
common difference. This is the entire carry argument. -/
theorem div_ap_of_base_factor {N d i e : ℕ} (hN : 0 < N)
    (hd : d = N ^ i * e) (a j : ℕ) :
    (a + j * d) / N ^ i = a / N ^ i + j * e := by
  rw [hd, Nat.mul_left_comm j (N ^ i) e]
  exact Nat.add_mul_div_left a (j * e) (pow_pos hN i)

/-- A digit is identified with its residue, so an extra remainder is redundant. -/
def digitColor {N : ℕ} {α : Type uAlpha} (C : ZMod N → α) (m : ℕ) :
    ℕ → (Fin m → α) :=
  fun n i => C ((n / N ^ i.val : ℕ) : ZMod N)

theorem digitColor_avoids {N k m : ℕ} {α : Type uAlpha} {C : ZMod N → α}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k) :
    ¬ HasMonoAP (digitColor C m) k (N ^ m) := by
  rintro ⟨a, d, hd, hbound, hmono⟩
  have hd_le : d ≤ (k - 1) * d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k - 1 by omega)
  have hd_bound : d < N ^ m := by omega
  obtain ⟨i, him, e, hde, he⟩ := exists_base_factor hd hd_bound
  have he_nonzero : (e : ZMod N) ≠ 0 := by
    intro hz
    exact he ((ZMod.natCast_eq_zero_iff e N).mp hz)
  apply hC ((a / N ^ i : ℕ) : ZMod N) (e : ZMod N) he_nonzero
  intro j hj
  have hcoord := congrFun (hmono j hj) (⟨i, him⟩ : Fin m)
  change C (((a + j * d) / N ^ i : ℕ) : ZMod N) =
    C ((a / N ^ i : ℕ) : ZMod N) at hcoord
  rw [div_ap_of_base_factor (by omega : 0 < N) hde a j] at hcoord
  simpa only [Nat.cast_add, Nat.cast_mul] using hcoord

/-- Explicit recoloring into any sufficiently large standard finite palette. -/
noncomputable def finiteColorEmbedding {α : Type uAlpha} [Fintype α] {r : ℕ}
    (h : Fintype.card α ≤ r) : α ↪ Fin r :=
  (Fintype.equivFin α).toEmbedding.trans (Fin.castLEEmb h)

theorem exists_digit_product_avoiding {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r) :
    ∃ c : ℕ → Fin r, ¬ HasMonoAP c k (N ^ m) := by
  classical
  have hcard : Fintype.card (Fin m → α) ≤ r := by
    rwa [Fintype.card_pi_const]
  let e := finiteColorEmbedding hcard
  refine ⟨e ∘ digitColor C m, ?_⟩
  exact not_hasMonoAP_of_recolor_injective e.injective (digitColor_avoids hN hk hC)

theorem digit_product_not_isRamsey {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r) : ¬ IsRamsey (Fin r) k (N ^ m) := by
  obtain ⟨c, hc⟩ := exists_digit_product_avoiding hN hk hC hcolors
  exact fun h => hc (h c)

/-- The finite witness is provided by the proved upper-bound construction. -/
theorem digit_product_lt_W {N k m r : ℕ} {α : Type uAlpha} [Fintype α]
    {C : ZMod N → α} (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hcolors : Fintype.card α ^ m ≤ r)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) : N ^ m < W r k := by
  exact lt_W_of_not_isRamsey hfinite (digit_product_not_isRamsey hN hk hC hcolors)

theorem binary_digit_product_lt_W {N k m : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin (2 ^ m)) k M) :
    N ^ m < W (2 ^ m) k := by
  apply digit_product_lt_W hN hk hC _ hfinite
  simp

theorem binary_digit_product_log_lt_W {N k r : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hr : 2 ≤ r) (hC : CyclicAvoids C k)
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M) :
    N ^ Nat.log 2 r < W r k := by
  apply digit_product_lt_W hN hk hC _ hfinite
  simpa using Nat.pow_log_le_self 2 (show r ≠ 0 by omega)

end QuantitativeVanDerWaerden

end OAI
