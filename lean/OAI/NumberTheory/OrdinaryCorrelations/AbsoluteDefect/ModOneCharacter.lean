import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.VerticalSeries
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PowerSumLe

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter

namespace OrdinaryCorrelations.PretentiousEuler
open Completion

lemma mod_one_character (n : ℕ) :
    (1 : DirichletCharacter ℂ 1) (n : ZMod 1)=1 := by
  rw [Subsingleton.elim (n : ZMod 1) 1,map_one]

lemma LSeries_complete_eq (f : ℕ → ℂ) (σ t : ℝ) :
    LSeries (complete f) ((σ:ℂ)+(t:ℂ)*Complex.I) =
      verticalSeries f (1 : DirichletCharacter ℂ 1) σ t := by
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn,LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero (show (n:ℂ)≠0 by exact_mod_cast hn),
      ←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n),
      mod_one_character,one_mul]
    rw [Real.rpow_def_of_pos (show (0:ℝ)<n by exact_mod_cast Nat.pos_of_ne_zero hn)]
    simp only [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.star_def,←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
      div_eq_mul_inv,←Complex.exp_neg,mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring

theorem compact_LSeries_saving {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ ∀ δ : ℝ, 0<δ → δ≤η → ∀t : ℝ, |t|≤T →
      ‖LSeries (complete f) ((1+δ:ℝ)+(t:ℂ)*Complex.I)‖ ≤ ε/δ := by
  obtain ⟨η,hη,hbound⟩ := compact_vertical_saving hf hNP (q:=1) (by norm_num)
    (1 : DirichletCharacter ℂ 1) T (half_pos hε)
  refine ⟨min η 1,lt_min hη zero_lt_one,min_le_right _ _,?_⟩
  intro δ hδ hδη t ht
  rw [LSeries_complete_eq]
  have he := hbound δ hδ (hδη.trans (min_le_left _ _)) t ht
  have hd1 : δ≤1 := hδη.trans (min_le_right _ _)
  calc
    _ ≤ _ := he
    _ ≤ (ε/2)*(1+1/δ) := mul_le_mul_of_nonneg_left
      (OrdinaryPowerBounds.power_sum_le hδ) (by positivity)
    _ ≤ ε/δ := by
      have hdiv : 1≤1/δ := (le_div_iff₀ hδ).mpr (by simpa using hd1)
      have he0 := hε.le
      simp only [div_eq_mul_inv, one_mul] at hdiv ⊢
      nlinarith [mul_nonneg he0 (sub_nonneg.mpr hdiv)]

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
