import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FactorialExp
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Alpha

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryChainScales
open OrdinaryExponentialBudgets

noncomputable def threshold (H j L : ℕ) : ℝ := Real.exp (-alpha H j*(L:ℝ))

lemma threshold_pos (H j L : ℕ) : 0<threshold H j L := Real.exp_pos _

lemma loss_absorption {A : ℝ} {B H s j K L M : ℕ}
    (hA : A+Real.exp 1+10≤(2:ℝ)^K)
    (hB : H+4*s+K+70≤B) (hL : E B s j≤L) (hM : M≤F B s (j+1)) :
    (A+Real.exp 1+10)*((amplifier L M:ℝ)+1)^2≤(mesh B H s (j+1):ℝ) := by
  have hh := amplifier_square_absorption B H s j K hB hL hM
  have hr : (2:ℝ)^K*((amplifier L M:ℝ)+1)^2≤(mesh B H s (j+1):ℝ) := by exact_mod_cast hh
  exact (mul_le_mul_of_nonneg_right hA (sq_nonneg _)).trans hr

lemma threshold_ratio (H j L M k : ℕ) :
    (threshold H (j+1) M)^2/(threshold H j L)^(2*k)=
    Real.exp (2*alpha H j*(k:ℝ)*(L:ℝ)-2*alpha H (j+1)*(M:ℝ)) := by
  unfold threshold
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_sub]
  congr 1
  push_cast
  ring

lemma transition_saving {A : ℝ} (hA0 : 0≤A) {B H s j K L M : ℕ}
    (hA : A+Real.exp 1+10≤(2:ℝ)^K)
    (hB : H+4*s+K+70≤B)
    (hL : E B s j≤L) (hL' : L≤F B s j)
    (hM : E B s (j+1)≤M) (hM' : M≤F B s (j+1)) :
    ((threshold H (j+1) M)^2/(threshold H j L)^(2*amplifier L M))*
    (A*(2+((amplifier L M:ℝ)+Real.log 2)^2)*(2:ℝ)^(amplifier L M)*
      ((amplifier L M).factorial:ℝ)*Real.exp ((amplifier L M:ℝ)+Real.exp 1-1))
      ≤ Real.exp (-999*(mesh B H s (j+1):ℝ)) := by
  rw [threshold_ratio]
  have he := amplification_weight_bound hA0 (amplifier L M)
  have hg := alpha_transition (show H+10≤B by omega) hL hL' hM
  have ha := loss_absorption hA hB hL hM'
  calc
    _ ≤ Real.exp (2*alpha H j*(amplifier L M:ℝ)*(L:ℝ)-2*alpha H (j+1)*(M:ℝ))*
      Real.exp ((A+Real.exp 1+10)*((amplifier L M:ℝ)+1)^2) :=
        mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = Real.exp ((2*alpha H j*(amplifier L M:ℝ)*(L:ℝ)-2*alpha H (j+1)*(M:ℝ))+
      (A+Real.exp 1+10)*((amplifier L M:ℝ)+1)^2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hg,ha])

end OrdinaryChainScales

end

end OAI
