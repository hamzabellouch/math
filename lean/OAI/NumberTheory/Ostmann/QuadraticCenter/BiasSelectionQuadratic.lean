import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import OAI.NumberTheory.Ostmann.Characters.QuadraticClassification
import OAI.NumberTheory.Ostmann.Preliminaries.WindowTestStability

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

def quadraticReal (p : ℕ) [Fact p.Prime] (x : ZMod p) : ℝ :=
  (quadraticChar (ZMod p) x : ℤ)

lemma quadraticCharacter_eq_real (x : ZMod p) :
    quadraticCharacter p x = (quadraticReal p x : ℂ) := by
  simp [quadraticCharacter, quadraticReal, MulChar.ringHomComp_apply]

lemma abs_quadraticReal_le_one (x : ZMod p) : |quadraticReal p x| ≤ 1 := by
  classical
  unfold quadraticReal
  rw [quadraticChar_apply]
  unfold quadraticCharFun
  split_ifs <;> norm_num

lemma norm_quadraticCharacter_le_one (x : ZMod p) :
    ‖quadraticCharacter p x‖ ≤ 1 := by
  rw [quadraticCharacter_eq_real, Complex.norm_real, Real.norm_eq_abs]
  exact abs_quadraticReal_le_one x

lemma quadraticReal_intCast (a : ℤ) :
    quadraticReal p (a : ZMod p) = (jacobiSym a p : ℝ) := by
  change (legendreSym p a : ℝ) = _
  rw [jacobiSym.legendreSym.to_jacobiSym]

def quadraticResidueMean (S : Finset (ZMod p)) (t : ZMod p) : ℝ :=
  (∑ x ∈ S, quadraticReal p (x - t)) / S.card

lemma translatedMean_quadratic_eq_real (S : Finset (ZMod p)) (t : ZMod p) :
    translatedMean S (quadraticCharacter p) t = (quadraticResidueMean S t : ℂ) := by
  simp only [translatedMean, quadraticResidueMean, quadraticCharacter_eq_real]
  push_cast
  ring

lemma exists_max_quadratic_translation (S : Finset (ZMod p)) :
    ∃ t : ZMod p, (maxTranslatedBias S (quadraticCharacter p) : ℝ) =
      |quadraticResidueMean S t| := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun t : ZMod p => ‖translatedMean S (quadraticCharacter p) t‖₊)
  refine ⟨t, ?_⟩
  change ((Finset.univ.sup _ : NNReal) : ℝ) = _
  rw [ht]
  change ‖translatedMean S (quadraticCharacter p) t‖ = _
  rw [translatedMean_quadratic_eq_real, Complex.norm_real, Real.norm_eq_abs]

lemma sum_quadraticReal_translate (hp : p ≠ 2) (t : ZMod p) :
    (∑ x : ZMod p, quadraticReal p (x - t)) = 0 := by
  have hcomplex : (∑ x : ZMod p, quadraticCharacter p (x - t)) = 0 := by
    calc
      _ = ∑ x : ZMod p, quadraticCharacter p x :=
        Fintype.sum_equiv (Equiv.subRight t) _ _ (fun _ => rfl)
      _ = 0 := MulChar.sum_eq_zero_of_ne_one (quadraticCharacter_ne_one p hp)
  simp only [quadraticCharacter_eq_real] at hcomplex
  exact_mod_cast hcomplex

lemma quadraticResidueMean_compl (S : Finset (ZMod p))
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) (hp : p ≠ 2) (t : ZMod p) :
    (S.card : ℝ) * quadraticResidueMean S t +
      (Sᶜ.card : ℝ) * quadraticResidueMean Sᶜ t = 0 := by
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have ht0 : (Sᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  unfold quadraticResidueMean
  rw [mul_div_cancel₀ _ hs0, mul_div_cancel₀ _ ht0]
  rw [Finset.sum_add_sum_compl]
  exact sum_quadraticReal_translate hp t

def biasOrientation (m : ℝ) : ℤ := if 0 ≤ m then 1 else -1

lemma biasOrientation_sign (m : ℝ) : biasOrientation m = 1 ∨ biasOrientation m = -1 := by
  unfold biasOrientation
  split_ifs <;> simp

lemma biasOrientation_mul (m : ℝ) : (biasOrientation m : ℝ) * m = |m| := by
  unfold biasOrientation
  split_ifs with hm
  · simp [abs_of_nonneg hm]
  · simp [abs_of_neg (lt_of_not_ge hm)]

end Ostmann.QuadraticCenter

end

end OAI
