import OAI.Combinatorics.Ryser.Incidence.WalkCounts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_dense_neighborhood
    (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hG : G ⊆ A ×ˢ B) {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ)) :
    ∃ b ∈ B,
      n / (2 * V ^ 2) ≤ ((neighbors A G b).card : ℝ) ∧
      ((badPairs (neighbors A G b) B G (n / (512 * V ^ 8))).card : ℝ) ≤
        ((neighbors A G b).card : ℝ) ^ 2 / 16 := by
  classical
  have hVpos : 0 < V := by linarith
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hVn : 0 < V * n := mul_pos hVpos hn
  let c : ℝ := n / (2 * V ^ 2)
  let t : ℝ := n / (512 * V ^ 8)
  let U : ℝ := n ^ 2 / (256 * V ^ 4)
  let d : β → ℝ := fun b => ((neighbors A G b).card : ℝ)
  let H : Finset β := B.filter fun b => c ≤ d b
  let L : Finset β := B.filter fun b => ¬c ≤ d b
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have htwice : n ^ 2 / V = 2 * ((V * n) * c) := by
    dsimp [c]
    field_simp [hVne]
  have havg : (V * n) ^ 2 * t = c * U := by
    dsimp [c, t, U]
    field_simp [hVne]; ring
  have hscale : 64 * U = c ^ 2 := by
    dsimp [c, U]
    field_simp [hVne]; ring
  have hdeg (b : β) : d b ≤ V * n := by
    exact (show ((neighbors A G b).card : ℝ) ≤ (A.card : ℝ) from
      Nat.cast_le.mpr (Finset.card_le_card (neighbors_subset A G b))).trans hA
  have hsum_edges : (G.card : ℝ) = ∑ b ∈ B, d b := by
    simpa only [d, Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) (card_edges_eq_sum_neighbors A B G hG)
  have hsplit : (∑ b ∈ H, d b) + (∑ b ∈ L, d b) = ∑ b ∈ B, d b := by
    exact Finset.sum_filter_add_sum_filter_not B (fun b => c ≤ d b) d
  have hhigh : (∑ b ∈ H, d b) ≤ (H.card : ℝ) * (V * n) := by
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul H d (V * n) (fun b _ => hdeg b)
  have hlow : (∑ b ∈ L, d b) ≤ (V * n) * c := by
    calc
      (∑ b ∈ L, d b) ≤ (L.card : ℝ) * c := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul L d c (fun b hb =>
            (lt_of_not_ge (Finset.mem_filter.mp hb).2).le)
      _ ≤ (B.card : ℝ) * c :=
        mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hc.le
      _ ≤ (V * n) * c := mul_le_mul_of_nonneg_right hB hc.le
  have htotal : n ^ 2 / V ≤ (H.card : ℝ) * (V * n) + (V * n) * c := by
    calc
      n ^ 2 / V ≤ (G.card : ℝ) := hE
      _ = (∑ b ∈ H, d b) + (∑ b ∈ L, d b) := hsum_edges.trans hsplit.symm
      _ ≤ (H.card : ℝ) * (V * n) + (V * n) * c := add_le_add hhigh hlow
  have hHcard : c ≤ (H.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hVn).mp
    nlinarith only [htotal, htwice]
  have hH : H.Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (hc.trans_le hHcard))
  have hbadcard : ((badPairs A B G t).card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    have hnat : (badPairs A B G t).card ≤ A.card * A.card := by
      calc
        (badPairs A B G t).card ≤ (A ×ˢ A).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = A.card * A.card := Finset.card_product A A
    exact_mod_cast (show (badPairs A B G t).card ≤ A.card ^ 2 by
      simpa only [pow_two] using hnat)
  have hcount :
      (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) =
        ∑ p ∈ badPairs A B G t, ((commonNeighbors B G p.1 p.2).card : ℝ) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) (sum_localBad_card_eq_sum_common A B G t)
  have hbad : (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) ≤ c * U := by
    calc
      (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) =
          ∑ p ∈ badPairs A B G t, ((commonNeighbors B G p.1 p.2).card : ℝ) := hcount
      _ ≤ ((badPairs A B G t).card : ℝ) * t := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (badPairs A B G t)
            (fun p => ((commonNeighbors B G p.1 p.2).card : ℝ)) t
            (fun p hp => (Finset.mem_filter.mp hp).2.le)
      _ ≤ (A.card : ℝ) ^ 2 * t := mul_le_mul_of_nonneg_right hbadcard ht
      _ ≤ (V * n) ^ 2 * t := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hA 2) ht
      _ = c * U := havg
  have hsmall : (∑ b ∈ H, ((localBad A B G t b).card : ℝ)) ≤ (H.card : ℝ) * U := by
    calc
      (∑ b ∈ H, ((localBad A B G t b).card : ℝ)) ≤
          ∑ b ∈ B, ((localBad A B G t b).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun b _ _ => Nat.cast_nonneg _)
      _ ≤ c * U := hbad
      _ ≤ (H.card : ℝ) * U := mul_le_mul_of_nonneg_right hHcard hU
  obtain ⟨b, hb, hlocal⟩ := Finset.exists_le_of_sum_le
    (s := H) (f := fun b => ((localBad A B G t b).card : ℝ))
    (g := fun _ => U) hH
    (by simpa only [Finset.sum_const, nsmul_eq_mul] using hsmall)
  have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
  have hcb : c ≤ d b := (Finset.mem_filter.mp hb).2
  have hsquare : c ^ 2 ≤ (d b) ^ 2 := pow_le_pow_left₀ hc.le hcb 2
  have hbound : U ≤ (d b) ^ 2 / 16 := by
    nlinarith only [hscale, hsquare, sq_nonneg (d b)]
  refine ⟨b, hbB, hcb, ?_⟩
  change ((badPairs (neighbors A G b) B G t).card : ℝ) ≤ (d b) ^ 2 / 16
  rw [← localBad_eq_badPairs_neighbors A B G t b]
  exact hlocal.trans hbound

end RyserCoveringCounterexample.Incidence

end OAI
