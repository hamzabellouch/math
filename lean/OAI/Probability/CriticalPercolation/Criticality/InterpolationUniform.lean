import Mathlib

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation

def interpolationConstant (c ε : ℝ) : ℝ :=
  (4*(16/(2*ε*ε))+6)*(1+Real.log 8+max 0 (Real.log (1/c))) +
    (2*(16/(2*ε*ε))+5)*Real.log 4

lemma interpolationConstant_pos (c : ℝ) {ε : ℝ} (hε : 0<ε) :
    0 < interpolationConstant c ε := by
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hm : 0 ≤ max 0 (Real.log (1/c)) := le_max_left _ _
  unfold interpolationConstant
  positivity

lemma interpolation_uniform_algebra {p c ε δ : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-p)
    (hδ : 0<δ) (hδ1 : δ≤1) (n : ℕ) :
    (4*(16/(2*p*(1-p)))+6)*(Real.log (1/δ)+n*(Real.log 8+Real.log (1/c))) +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 ≤
      interpolationConstant c ε * (Real.log (1/δ)+n+1) := by
  have h4 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1:ℝ)<4)).le
  have h8 : 0 ≤ Real.log 8 := (Real.log_pos (by norm_num : (1:ℝ)<8)).le
  have hr : 0 ≤ Real.log (1/δ) := by
    rw [one_div,Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  have hc' : 0 ≤ Real.log (1/c) := by
    rw [one_div,Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hc.le hc1)
  have hK : 16/(2*p*(1-p)) ≤ 16/(2*ε*ε) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh := mul_le_mul hεp hεq hε.le hp.1.le
    nlinarith
  let A : ℝ := 4*(16/(2*ε*ε))+6
  let B : ℝ := 2*(16/(2*ε*ε))+5
  let l : ℝ := Real.log 8+max 0 (Real.log (1/c))
  let r : ℝ := Real.log (1/δ)
  let T : ℝ := r+n+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hl : 0 ≤ l := add_nonneg h8 (le_max_left _ _)
  have hcoef : 0 ≤ A*l+B*Real.log 4 := add_nonneg (mul_nonneg hA hl) (mul_nonneg hB h4)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hrT : r≤T := by dsimp [T]; linarith
  have hnT : (n:ℝ)≤T := by dsimp [T,r]; linarith
  calc
    _ ≤ A*(r+n*(Real.log 8+Real.log (1/c)))+B*(n*Real.log 4) := by
      rw [mul_assoc _ (n:ℝ) (Real.log 4)]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
        · dsimp [A]; linarith
        · exact add_nonneg hr (mul_nonneg hn (add_nonneg h8 hc'))
      · apply mul_le_mul_of_nonneg_right
        · dsimp [B]; linarith
        · exact mul_nonneg hn h4
    _ ≤ A*(r+n*l)+B*(n*Real.log 4) := by
      apply add_le_add ?_ le_rfl
      apply mul_le_mul_of_nonneg_left _ hA
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_right _ _)) hn
    _ = A*r+(A*l+B*Real.log 4)*n := by ring
    _ ≤ A*T+(A*l+B*Real.log 4)*T :=
      add_le_add (mul_le_mul_of_nonneg_left hrT hA) (mul_le_mul_of_nonneg_left hnT hcoef)
    _ = _ := by dsimp [A,B,l,r,T,interpolationConstant]; ring

end CriticalPercolation
end
end
end

end OAI
