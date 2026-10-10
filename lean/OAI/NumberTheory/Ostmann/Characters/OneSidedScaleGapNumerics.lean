import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Filter
open scoped Topology

theorem longProfileBudget_le_exponentials {atom rows E b amp prime P s u c t : ℝ}
    (n : ℕ) (_hatom0 : 0 ≤ atom) (hrows0 : 0 ≤ rows) (hE0 : 0 ≤ E)
    (hb : 0 < b) (hamp0 : 0 ≤ amp) (hprime0 : 0 ≤ prime)
    (hatom : atom ≤ Real.exp (-c*t)) (hrows : rows ≤ Real.exp P)
    (hE : E ≤ Real.exp P) (hamp : amp ≤ Real.exp P)
    (hprime : prime ≤ Real.exp s) (hlong : Real.exp u ≤ b) :
    atom*(3*rows*E*amp^2) + rows*prime^2*(E/b)*Real.exp (((n:ℝ)+2)*P) ≤
      Real.exp (Real.log 3+4*P-c*t) + Real.exp (((n:ℝ)+4)*P+2*s-u) := by
  apply add_le_add
  · calc
      _ ≤ Real.exp (-c*t)*(3*Real.exp P*Real.exp P*(Real.exp P)^2) := by gcongr
      _ = _ := by
        rw [show (3 : ℝ) = Real.exp (Real.log 3) from (Real.exp_log (by norm_num)).symm]
        simp only [Real.log_exp,← Real.exp_nat_mul,← Real.exp_add]
        congr 1
        ring
  · calc
      _ ≤ Real.exp P*(Real.exp s)^2*(Real.exp P/Real.exp u)*Real.exp (((n:ℝ)+2)*P) := by gcongr
      _ = _ := by
        simp only [← Real.exp_nat_mul,← Real.exp_sub,← Real.exp_add]
        congr 1
        ring

theorem historyBudget_exponents_le (C z : ℝ) (d n : ℕ) (L : ℝ) (hC : 0 ≤ C) :
    Real.log 3 + 4*historyPolynomialCost C z d L ≤
      historyPolynomialCost (((n:ℝ)+6)*C+2) z d L ∧
    ((n:ℝ)+4)*historyPolynomialCost C z d L ≤
      historyPolynomialCost (((n:ℝ)+6)*C+2) z d L := by
  have hbase : 1 ≤ (1+(⌊z*L⌋₊ : ℝ))^d := one_le_pow₀ (by have hh : (0 : ℝ) ≤ (⌊z*L⌋₊ : ℝ) := Nat.cast_nonneg _; linarith)
  have hp : 0 ≤ C*(1+(⌊z*L⌋₊ : ℝ))^d := mul_nonneg hC (by positivity)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hl : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  unfold historyPolynomialCost
  constructor <;> nlinarith [mul_nonneg hn hp]

theorem eventually_history_budget_decay (C z : ℝ) (d n : ℕ)
    {α β γ c : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C) (hα : 0 < α) (hαβ : α ≤ β)
    (hβγ : β < γ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, 0 ≤ x →
      x^2 ≤ Real.exp (Real.log 3+4*historyPolynomialCost C z d L-c*Real.exp (α*L)) +
        Real.exp (((n:ℝ)+4)*historyPolynomialCost C z d L+2*Real.exp (β*L)-Real.exp (γ*L)) →
      x ≤ Real.exp (-δ*Real.exp (α*L)) := by
  let ε : ℝ := min (c/2) 1
  have hε : 0 < ε := lt_min (half_pos hc) (by norm_num)
  refine ⟨ε/4,by positivity,?_⟩
  have hg := eventually_history_scale_gap_exponents (((n:ℝ)+6)*C+2) z d hz hα hαβ hβγ hc
  have ht : Tendsto (fun L : ℝ => Real.exp (α*L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)
  filter_upwards [hg,ht.eventually (eventually_ge_atTop (2*Real.log 2/ε))] with L hgap hlarge
  intro x hx hx2
  have hpoly := historyBudget_exponents_le C z d n L hC
  have he1 : Real.log 3+4*historyPolynomialCost C z d L-c*Real.exp (α*L) ≤
      -ε*Real.exp (α*L) := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left (c/2) 1) (Real.exp_pos (α*L)).le
    dsimp only [ε]
    linarith [hgap.1,hpoly.1]
  have he2 : ((n:ℝ)+4)*historyPolynomialCost C z d L+2*Real.exp (β*L)-Real.exp (γ*L) ≤
      -ε*Real.exp (α*L) := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (c/2) 1) (Real.exp_pos (α*L)).le
    dsimp only [ε]
    linarith [hgap.2,hpoly.2]
  have hlarge' := (div_le_iff₀ hε).mp hlarge
  have hsq : x^2 ≤ (Real.exp (-(ε/4)*Real.exp (α*L)))^2 := by
    calc
      _ ≤ 2*Real.exp (-ε*Real.exp (α*L)) := by
        linarith [Real.exp_le_exp.mpr he1,Real.exp_le_exp.mpr he2]
      _ = Real.exp (Real.log 2-ε*Real.exp (α*L)) := by
        rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
        simp only [neg_mul,Real.exp_neg,div_eq_mul_inv]
      _ ≤ Real.exp (-(ε/2)*Real.exp (α*L)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  nlinarith [Real.exp_pos (-(ε/4)*Real.exp (α*L))]

end Ostmann.Characters

end

end OAI
