import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction Conclusion Filter ScaleBudget HistoryUnnormalizedFlagError

theorem selected_square_loss_budget_eventually (k : ℕ) (A D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ outside : List ℕ,
      (∀ p ∈ outside, 0 < p) → outside.length ≤ bulkSize k L →
      (∀ p ∈ outside, Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1))) *
        Real.exp (D*(L+1)^2) *
        ((4*k*2^k:ℕ)*Real.exp (-Real.exp ((39/10000:ℝ)*L))) *
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
      Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  let n : ℝ := (4*k*2^k:ℕ)
  let R : ℝ := n+2*(2:ℝ)^k*(bulkScale k+1)
  let T : ℝ := spectatorCost k A+|D|+R
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hR : 0 ≤ R := by unfold R bulkScale; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity [spectatorCost_pos k A]
  filter_upwards [eventually_double_exp_error (4*T) 2
    (a:=11/10000) (b:=39/10000) (d:=1/500) (c:=1)
    (by norm_num) (by norm_num) (by norm_num),eventually_ge_atTop (1:ℝ)] with L he hL
  intro l hl outside hpos hlen hlog
  have hL0 : 0 ≤ L := by linarith
  have ho := spectator_prefactor_le hl hL0 A outside hpos hlen hlog
  have hn : n ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
  have hp : (2:ℝ)^l ≤ (2:ℝ)^k := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ)) hl
  have hb := (bulkSize_bounds k hL0).2
  have hs : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have hm : (bulkSize k L:ℝ) ≤ (bulkScale k+1)*(L+1) := by nlinarith
  have hk : 2*(2:ℝ)^l*(bulkSize k L:ℝ) ≤ 2*(2:ℝ)^k*((bulkScale k+1)*(L+1)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) hm
      (Nat.cast_nonneg _) (by positivity)
  have hne : n*Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤ Real.exp (R*(L+1)) := by
    calc
      _ ≤ Real.exp n*Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
      _ = Real.exp (n+2*(2:ℝ)^l*(bulkSize k L:ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; dsimp only [R]; nlinarith
  have hD : Real.exp (D*(L+1)^2) ≤ Real.exp (|D| *(L+1)^2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _))
  have hscale : 1 ≤ Real.exp ((11/10000:ℝ)*L) := Real.one_le_exp (by positivity)
  have hpoly : (L+1) ≤ (L+1)^2 := by nlinarith
  have hbound : commonLogBudget (spectatorCost k A) L+|D| *(L+1)^2+R*(L+1) ≤
      T*(L+1)^2*Real.exp ((11/10000:ℝ)*L) := by
    have hd := le_mul_of_one_le_right (mul_nonneg (abs_nonneg D) (sq_nonneg (L+1))) hscale
    have hr := (mul_le_mul_of_nonneg_left hpoly hR).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ R*(L+1)^2) hscale)
    dsimp only [T,commonLogBudget]
    nlinarith
  calc
    _ = ((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1))) *
        Real.exp (D*(L+1)^2) *
        (n*Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ))) *
        Real.exp (-Real.exp ((39/10000:ℝ)*L)) := by dsimp only [n]; ring
    _ ≤ Real.exp (commonLogBudget (spectatorCost k A) L)*
        Real.exp (|D| *(L+1)^2)*Real.exp (R*(L+1))*
        Real.exp (-Real.exp ((39/10000:ℝ)*L)) := by gcongr
    _ = Real.exp (commonLogBudget (spectatorCost k A) L+|D| *(L+1)^2+
        R*(L+1)-Real.exp ((39/10000:ℝ)*L)) := by
      rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 1
    _ ≤ Real.exp (4*T*L^2*Real.exp ((11/10000:ℝ)*L)-Real.exp ((39/10000:ℝ)*L)) := by
      apply Real.exp_le_exp.mpr
      have hq := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by nlinarith : (L+1)^2 ≤ 4*L^2) hT)
        (Real.exp_nonneg ((11/10000:ℝ)*L))
      linarith
    _ ≤ _ := by simpa only [neg_mul,one_mul,sub_eq_add_neg,add_comm] using he

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
