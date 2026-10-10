import OAI.NumberTheory.Ostmann.Construction.NominalTotalsError

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

theorem nominalJ_bounds_of_small_errors (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k)
    {L G₀ c td : ℝ} (hG : 0≤G₀) (hh : 8≤favorableBlockWidth L)
    (hc : G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2)
    (htd : |td|≤favorableBlockWidth L/16)
    (hgap : nominalGapMagnitude Bs BD Bz k L≤favorableBlockWidth L/16) :
    favorableBlockWidth L/2≤nominalJ Bs BD Bz k L G₀ c td ∧
      nominalJ Bs BD Bz k L G₀ c td≤3*favorableBlockWidth L := by
  let h := favorableBlockWidth L
  let P : ℝ := (2:ℝ)^k
  have hP : 2≤P := by
    simpa only [pow_one,P] using
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1≤k from hk))
  have hPp : 0<P := by positivity
  have hE : 0≤2*G₀+(2:ℝ)^(k+1)*h := by positivity
  have hlo : 2*G₀+(2:ℝ)^(k+1)*h≤
      Real.log (giantWindowScale ((2:ℝ)^(k+1)) G₀ L:ℝ) := by
    have he := Real.log_le_log (Real.exp_pos (2*G₀+(2:ℝ)^(k+1)*h))
      (Nat.le_ceil (Real.exp (2*G₀+(2:ℝ)^(k+1)*h)))
    rw [Real.log_exp] at he
    exact he
  have hhi := log_ceil_exp_le_add_one (2*G₀+(2:ℝ)^(k+1)*h) hE
  change Real.log (giantWindowScale ((2:ℝ)^(k+1)) G₀ L:ℝ)≤2*G₀+(2:ℝ)^(k+1)*h+1 at hhi
  have habs : |Conclusion.initialGap Bs k L+∑j∈Finset.range k,Conclusion.stepGap BD Bz k L j|≤h/16 := by
    apply le_trans (abs_add_le _ _) 
    apply le_trans (add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _))
    exact hgap
  have hab := abs_le.mp habs
  have htd' := abs_le.mp htd
  change 8≤h at hh
  change G₀-2≤c ∧ c≤G₀+h+2 at hc
  change -(h/16)≤td ∧ td≤h/16 at htd'
  rw [pow_succ] at hlo hhi
  change 2*G₀+P*2*h≤_ at hlo
  change _≤2*G₀+P*2*h+1 at hhi
  unfold nominalJ
  rw [pow_succ]
  change h/2≤_ / P ∧ _ / P≤3*h
  constructor
  · apply (le_div_iff₀ hPp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hh)]
  · apply (div_le_iff₀ hPp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hh)]

theorem nominalTotals_bounds_of_small_errors (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k)
    {L G₀ c tb td : ℝ} (hG : 0≤G₀) (hh : 8≤favorableBlockWidth L)
    (hc : G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2)
    (htb : |tb|≤favorableBlockWidth L/16) (htd : |td|≤favorableBlockWidth L/16)
    (hgap : nominalGapMagnitude Bs BD Bz k L≤favorableBlockWidth L/16) :
    (favorableBlockWidth L/2≤nominalJ Bs BD Bz k L G₀ c td ∧
      nominalJ Bs BD Bz k L G₀ c td≤3*favorableBlockWidth L) ∧
    (favorableBlockWidth L/4≤nominalJ Bs BD Bz k L G₀ c td-2*tb ∧
      nominalJ Bs BD Bz k L G₀ c td-2*tb≤4*favorableBlockWidth L) ∧
    ∀j<k, favorableBlockWidth L/4≤nominalCompensation Bs BD Bz k L G₀ c td j ∧
      nominalCompensation Bs BD Bz k L G₀ c td j≤4*(2:ℝ)^k*favorableBlockWidth L := by
  have hJ := nominalJ_bounds_of_small_errors Bs BD Bz hk hG hh hc htd hgap
  have htb' := abs_le.mp htb
  refine ⟨hJ,⟨by linarith,by linarith⟩,?_⟩
  intro j hj
  have herr := nominalWeight_error_le hj (nominalJ Bs BD Bz k L G₀ c td)
    (Conclusion.stepGap BD Bz k L)
  have herr' : |nominalCompensation Bs BD Bz k L G₀ c td j-
      (2:ℝ)^(k-1-j)*nominalJ Bs BD Bz k L G₀ c td|≤favorableBlockWidth L/16 := by
    apply herr.trans
    apply le_trans _ hgap
    unfold nominalGapMagnitude
    exact le_add_of_nonneg_left (abs_nonneg _)
  have hb := abs_le.mp herr'
  have hp1 : (1:ℝ)≤2^(k-1-j) := one_le_pow₀ (by norm_num)
  have hp2 : (2:ℝ)^(k-1-j)≤2^k := pow_le_pow_right₀ (by norm_num) (by omega)
  have hJn : 0≤nominalJ Bs BD Bz k L G₀ c td := by linarith
  have hlo := mul_le_mul_of_nonneg_right hp1 hJn
  have hhi := mul_le_mul hp2 hJ.2 hJn (by positivity : (0:ℝ)≤2^k)
  have hPk : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  constructor
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hPk) (show 0≤favorableBlockWidth L by linarith)]

end Ostmann.Construction

end

end OAI
