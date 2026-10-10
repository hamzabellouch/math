import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlags
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistorySymbolicEncoding HistoryPairPattern HistoryPairRows HistoryPairFlags

def heightCoefficient (k : ℕ) : ℕ := historyCostCoefficient k+7*k*2^k+5

theorem heightCoefficient_pos (k : ℕ) : 0<heightCoefficient k := by
  unfold heightCoefficient
  omega

theorem height_exponents_le {b k l : ℕ} {h : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hl : l≤k) :
    2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)+5≤
      heightCoefficient k*(b+1) ∧
    2^l*(h.root.small.length+2*h.internalOccurrences.length)≤heightCoefficient k*(b+1) := by
  have hc := hh.cost_le hl
  have hp : (2:ℕ)^l≤2^k := Nat.pow_le_pow_right (by omega) hl
  have hx : 7*l*2^l≤7*k*2^k := Nat.mul_le_mul (Nat.mul_le_mul_left 7 hl) hp
  constructor
  · calc
      _ = 2^l*(2+h.root.small.length+2*h.internalOccurrences.length)+(7*l*2^l)+5 := by ring
      _ ≤ historyCostCoefficient k*(b+1)+(7*k*2^k)+5 := by omega
      _ ≤ historyCostCoefficient k*(b+1)+(7*k*2^k+5)*(b+1) := by
        have hx' := Nat.mul_le_mul_left (7*k*2^k+5) (Nat.succ_le_succ (Nat.zero_le b))
        simp only [Nat.succ_eq_add_one] at hx'
        omega
      _ = _ := by unfold heightCoefficient; ring
  · exact (Nat.mul_le_mul_left (2^l) (by omega :
      h.root.small.length+2*h.internalOccurrences.length≤2+h.root.small.length+2*h.internalOccurrences.length)).trans
      (hc.trans (Nat.mul_le_mul_right (b+1) (by unfold heightCoefficient; omega)))

theorem height_log_le {b k l : ℕ} {h : History l} (V : ℕ→ℕ) {B : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hl : l≤k) (hB : 1≤B) :
    Real.log (HistoryPatternFlagBounds.height h V B) ≤
      (heightCoefficient k:ℝ)*(b+1)*
        (Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l)+Real.log B) := by
  have hF := HistoryHeightBudgetFixed.one_le_frequencyBound V l
  have hFpos : 0<HistoryHeightBudgetFixed.frequencyBound V l := by linarith
  have hBpos : 0<B := by linarith
  have he := height_exponents_le hh hl
  have he₁ : ((2^l*(2+h.root.small.length+2*h.internalOccurrences.length+7*l)+5:ℕ):ℝ)≤
      (heightCoefficient k:ℝ)*(b+1) := by exact_mod_cast he.1
  have he₂ : ((2^l*(h.root.small.length+2*h.internalOccurrences.length):ℕ):ℝ)≤
      (heightCoefficient k:ℝ)*(b+1) := by exact_mod_cast he.2
  rw [HistoryPatternFlagBounds.height,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_mul (by norm_num) hFpos.ne']
  have hlogF : 0≤Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l) :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hF)
  have hlogB := Real.log_nonneg hB
  calc
    _ ≤ ((heightCoefficient k:ℝ)*(b+1))*(Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l))+
        ((heightCoefficient k:ℝ)*(b+1))*Real.log B :=
      add_le_add (mul_le_mul_of_nonneg_right he₁ hlogF) (mul_le_mul_of_nonneg_right he₂ hlogB)
    _ = _ := by ring

theorem height_one_le {l : ℕ} (h : History l) (V : ℕ→ℕ) {B : ℝ} (hB : 1≤B) :
    1≤HistoryPatternFlagBounds.height h V B := by
  have hF := HistoryHeightBudgetFixed.one_le_frequencyBound V l
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by linarith : 1≤2*HistoryHeightBudgetFixed.frequencyBound V l)
  · exact one_le_pow₀ hB

theorem envelope_log_le {b k l : ℕ} {h g : History l} (V : ℕ→ℕ) {B : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l≤k) (hB : 1≤B) :
    max 0 (Real.log (envelope h g V B)) ≤
      Real.log 3+4*((heightCoefficient k:ℝ)*(b+1)*
        (Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l)+Real.log B)) := by
  let H := HistoryPairFlagBounds.height h g V B
  let X := (heightCoefficient k:ℝ)*(b+1)*
    (Real.log 2+Real.log (HistoryHeightBudgetFixed.frequencyBound V l)+Real.log B)
  have hH : 1≤H := (height_one_le h V hB).trans (le_max_left _ _)
  have hHp : 0<H := by linarith
  have hHX : H≤Real.exp X := max_le
    ((Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (height_one_le h V hB))).mp
      (height_log_le V hh hl hB))
    ((Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (height_one_le g V hB))).mp
      (height_log_le V hg hl hB))
  have hlogHX : Real.log H≤X := (Real.log_le_iff_le_exp hHp).mpr hHX
  have hX : 0≤X := (Real.log_nonneg hH).trans hlogHX
  have he : envelope h g V B≤3*H^4 := by
    change H^2+2*H^4≤3*H^4
    have hp : H^2≤H^4 := pow_le_pow_right₀ hH (by omega)
    linarith
  have hep : 0<envelope h g V B := by
    change 0<H^2+2*H^4
    positivity
  have hlog : Real.log (envelope h g V B)≤Real.log 3+4*X := by
    calc
      _ ≤ Real.log (3*H^4) := Real.log_le_log hep he
      _ = Real.log 3+4*Real.log H := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hHp.ne'),Real.log_pow]; norm_num
      _ ≤ _ := by linarith
  exact max_le (by have := Real.log_nonneg (by norm_num : (1:ℝ)≤3); linarith) hlog

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
