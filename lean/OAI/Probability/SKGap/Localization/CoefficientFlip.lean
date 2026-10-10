import Mathlib
import OAI.Probability.SKGap.Localization.Taylor
import OAI.Probability.SKGap.Localization.ScalarVariance

namespace OAI

section

noncomputable section
open Set
namespace SKGapCutoff.Recipe
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def flipHalfDiff (i : Fin n) (P : Spin n→E) (x : Spin n) : E :=
  (spin x i/2) • (P x-P (flip x i))

lemma flipHalfDiff_norm (i : Fin n) (P : Spin n→E) (x : Spin n) :
    ‖flipHalfDiff i P x‖=‖P (flip x i)-P x‖/2 := by
  simp only [flipHalfDiff,norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [norm_sub_rev]
  ring

lemma flipHalfDiff_real (i : Fin n) (P : Spin n→ℝ) (x : Spin n) :
    flipHalfDiff i P x=halfDiff i P x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,smul_eq_mul]
  ring

lemma coefficient_linearization (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (T : E→L[ℝ]ℝ) :
    halfDiff i (fun y=>F (P y)) x-T (flipHalfDiff i P x)=
      (-spin x i/2)*(F (P (flip x i))-F (P x)-T (P (flip x i)-P x)) := by
  rw [halfDiff_as_flip]
  simp only [flipHalfDiff,map_smul,map_sub,smul_eq_mul]
  ring

lemma coefficient_taylor (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {L : ℝ} (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,
      ‖F' (P x+t • (P (flip x i)-P x))-F' (P x)‖≤L*‖t • (P (flip x i)-P x)‖) :
    |halfDiff i (fun y=>F (P y)) x-F' (P x) (flipHalfDiff i P x)|≤
      2*L*‖flipHalfDiff i P x‖^2 := by
  have H:=SKGap.SourceTaylor.segment_taylor F F' (P x) (P (flip x i)) hL hF hLip
  rw [coefficient_linearization,abs_mul,abs_div,abs_neg,abs_spin_eq_one,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm]
  calc
    _ ≤ (1/2:ℝ)*(L*‖P (flip x i)-P x‖^2) := mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring

lemma coefficient_lipschitz (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (P x+t • (P (flip x i)-P x))‖≤C) :
    |halfDiff i (fun y=>F (P y)) x|≤C*‖flipHalfDiff i P x‖ := by
  have H:=SKGap.SourceTaylor.segment_lipschitz F F' (P x) (P (flip x i)) hC hF hBound
  rw [halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right H (show (0:ℝ)≤2 by norm_num)

end SKGapCutoff.Recipe

end
end

end OAI
