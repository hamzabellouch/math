import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion Filter ScaleBudget HistoryUnnormalizedFlagError

theorem ordered_bulk_card_le {k l : ℕ} (hl : l ≤ k) {L : ℝ} (hL : 0 ≤ L) :
    ((2^l*(2*(bulkSize k L/2)) : ℕ) : ℝ) ≤
      ((2:ℝ)^k*(bulkScale k+1))*(L+1) := by
  have hp : ((2^l:ℕ):ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hl
  have hm : ((2*(bulkSize k L/2):ℕ):ℝ) ≤ bulkSize k L := by
    exact_mod_cast (by omega : 2*(bulkSize k L/2) ≤ bulkSize k L)
  have hb := (bulkSize_bounds k hL).2
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have hml : ((2*(bulkSize k L/2):ℕ):ℝ) ≤ (bulkScale k+1)*(L+1) := by nlinarith
  rw [Nat.cast_mul]
  exact (mul_le_mul hp hml (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)

theorem selected_collision_budget_eventually (k : ℕ) (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ outside : List ℕ,
      (∀ p ∈ outside, 0 < p) → outside.length ≤ bulkSize k L →
      (∀ p ∈ outside, Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ((outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1))) *
        Real.exp (D*(L+1)^2) * ((2^l*(2*(bulkSize k L/2)):ℕ):ℝ)^2 *
        Real.exp (L-Real.exp ((39/10000:ℝ)*L)) ≤
      Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  let R : ℝ := (2:ℝ)^k*(bulkScale k+1)
  let T : ℝ := spectatorCost k C + |D| + 2*R + 1
  have hR : 0 ≤ R := by unfold R bulkScale; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity [spectatorCost_pos k C]
  filter_upwards [eventually_double_exp_error (4*T) 2
    (a:=11/10000) (b:=39/10000) (d:=1/500) (c:=1)
    (by norm_num) (by norm_num) (by norm_num), eventually_ge_atTop (1:ℝ)] with L he hL
  intro l hl outside hpos hlen hlog
  have hL0 : 0 ≤ L := by linarith
  have ho := spectator_prefactor_le hl hL0 C outside hpos hlen hlog
  let n : ℝ := ((2^l*(2*(bulkSize k L/2)):ℕ):ℝ)
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hn : n ≤ R*(L+1) := ordered_bulk_card_le hl hL0
  have hne : n^2 ≤ Real.exp (2*R*(L+1)) := by
    calc
      n^2 ≤ (Real.exp n)^2 := pow_le_pow_left₀ hn0 (by linarith [Real.add_one_le_exp n]) 2
      _ = Real.exp (2*n) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hD : Real.exp (D*(L+1)^2) ≤ Real.exp (|D| *(L+1)^2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _))
  have hscale : Real.exp ((11/10000:ℝ)*L) ≥ 1 := Real.one_le_exp (by positivity)
  have hpoly : (L+1) ≤ (L+1)^2 := by nlinarith
  have hbound : commonLogBudget (spectatorCost k C) L + |D| *(L+1)^2 +
      2*R*(L+1)+L ≤ T*(L+1)^2*Real.exp ((11/10000:ℝ)*L) := by
    have hd := le_mul_of_one_le_right (mul_nonneg (abs_nonneg D) (sq_nonneg (L+1))) hscale
    have hr := (mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 2*R)).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ 2*R*(L+1)^2) hscale)
    have hl' : L ≤ (L+1)^2*Real.exp ((11/10000:ℝ)*L) :=
      (by nlinarith : L ≤ (L+1)^2).trans (le_mul_of_one_le_right (sq_nonneg _) hscale)
    dsimp only [T, commonLogBudget]
    nlinarith
  calc
    _ ≤ Real.exp (commonLogBudget (spectatorCost k C) L) *
        Real.exp (|D| *(L+1)^2) * Real.exp (2*R*(L+1)) *
        Real.exp (L-Real.exp ((39/10000:ℝ)*L)) := by
      dsimp only [n] at hne
      gcongr
    _ = Real.exp (commonLogBudget (spectatorCost k C) L+|D| *(L+1)^2+
        2*R*(L+1)+L-Real.exp ((39/10000:ℝ)*L)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (4*T*L^2*Real.exp ((11/10000:ℝ)*L)-Real.exp ((39/10000:ℝ)*L)) := by
      apply Real.exp_le_exp.mpr
      have hq := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by nlinarith : (L+1)^2 ≤ 4*L^2) hT)
        (Real.exp_nonneg ((11/10000:ℝ)*L))
      nlinarith
    _ ≤ _ := by simpa only [neg_mul, one_mul, sub_eq_add_neg, add_comm] using he

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
