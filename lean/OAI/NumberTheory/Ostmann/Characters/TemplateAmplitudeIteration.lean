import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateAmplitudeIteration

def penalty (b : ℝ) (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => b
  | j+1 => 2*penalty b d j+d j+Real.log 2

theorem penalty_le_total (b : ℝ) (d : ℕ → ℝ) (hd : ∀j,0≤d j) (j : ℕ) :
    penalty b d j ≤ (2:ℝ)^j*(b+∑h∈Finset.range j,(d h+Real.log 2)) := by
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  induction j with
  | zero => simp [penalty]
  | succ j ih =>
    have hc : 0≤d j+Real.log 2 := add_nonneg (hd j) hlog
    have hp : 1≤(2:ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    rw [penalty,Finset.sum_range_succ]
    calc
      _ ≤ 2*((2:ℝ)^j*(b+∑h∈Finset.range j,(d h+Real.log 2)))+(d j+Real.log 2) := by linarith
      _ ≤ (2:ℝ)^(j+1)*(b+(∑h∈Finset.range j,(d h+Real.log 2))+(d j+Real.log 2)) := by
        have hh := mul_le_mul_of_nonneg_right hp hc
        rw [pow_succ] at hh ⊢
        nlinarith
      _ = _ := by ring

theorem exp_neg_penalty_step (b : ℝ) (d : ℕ → ℝ) (j : ℕ) :
    Real.exp (-penalty b d (j+1))=
      (1/2:ℝ)*Real.exp (-d j)*(Real.exp (-penalty b d j))^2 := by
  have he : -penalty b d (j+1)= -Real.log 2+(-d j)+(-penalty b d j+-penalty b d j) := by
    rw [penalty]
    ring
  rw [he,Real.exp_add,Real.exp_add,Real.exp_add]
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
  ring

theorem amplitude_budget (k : ℕ) (B0 B1 m : ℝ) (η d D : ℕ → ℝ)
    (hd : ∀j,0≤d j)
    (hbudget : (∑j∈Finset.range k,(d j+Real.log 2))≤(B1-B0)*m)
    (hinitial : Real.exp (-B0*m)≤η 0)
    (htransfer : ∀j<k,(η j)^2≤Real.exp (d j)*(D j+η (j+1)))
    (hdiag : ∀j<k,D j≤(1/2:ℝ)*Real.exp (-d j)*Real.exp (-2*B1*(2:ℝ)^j*m)) :
    ∀j≤k,Real.exp (-B1*(2:ℝ)^j*m)≤η j := by
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hp (j : ℕ) (hj : j≤k) : penalty (B0*m) d j≤B1*(2:ℝ)^j*m := by
    have hs : (∑h∈Finset.range j,(d h+Real.log 2))≤∑h∈Finset.range k,(d h+Real.log 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        (fun h _ _ => add_nonneg (hd h) hlog)
    have hh := mul_le_mul_of_nonneg_left (hs.trans hbudget) (pow_nonneg (by norm_num : (0:ℝ)≤2) j)
    have hpen := penalty_le_total (B0*m) d hd j
    nlinarith
  have hactual (j : ℕ) (hj : j≤k) : Real.exp (-penalty (B0*m) d j)≤η j := by
    induction j with
    | zero => simpa only [penalty,neg_mul] using hinitial
    | succ j ih =>
      have hjk : j<k := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have hjle : j≤k := hjk.le
      have hi := ih hjle
      have hs : (Real.exp (-penalty (B0*m) d j))^2≤(η j)^2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le hi 2
      have hrec : Real.exp (-d j)*(η j)^2≤D j+η (j+1) := by
        have hh := mul_le_mul_of_nonneg_left (htransfer j hjk) (Real.exp_pos (-d j)).le
        calc
          _ ≤ Real.exp (-d j)*(Real.exp (d j)*(D j+η (j+1))) := hh
          _ = _ := by rw [←mul_assoc,←Real.exp_add]; simp
      have hsmall : Real.exp (-2*B1*(2:ℝ)^j*m)≤(Real.exp (-penalty (B0*m) d j))^2 := by
        rw [←Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hh := hp j hjle
        norm_num
        nlinarith
      have hdiag' := (hdiag j hjk).trans
        (mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤(1/2:ℝ)*Real.exp (-d j)))
      have hsq := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-d j)).le
      rw [exp_neg_penalty_step]
      nlinarith
  intro j hj
  exact (Real.exp_le_exp.mpr (by have hh:=hp j hj; linarith)).trans (hactual j hj)

end Ostmann.Characters.TemplateAmplitudeIteration

end

end OAI
