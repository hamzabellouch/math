import Mathlib
import OAI.Analysis.LaughlinGap.HighestRatios
import OAI.Analysis.LaughlinGap.PairEndpoints
import OAI.Analysis.LaughlinGap.ThreeSpin

namespace OAI

/-! Three Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairSpectatorInclusion_transpose_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (x : ((Fin (Q+1) × Fin (Q+1)) × Fin (Q+1)) → ℝ)
    (p : Fin (2*Q-2+1)) (k : Fin (Q+1)) :
    (pairSpectatorInclusion hQ).transpose.toLinearMap x (p,k) =
      ∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q p.val i j * x ((i,j),k) := by
  classical
  change transposeMap (pairSpectatorInclusion hQ).toLinearMap x (p,k) = _
  simp only [transposeMap, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type]
  simp_rw [pairSpectatorInclusion_apply]
  simp only [Prod.mk.injEq, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  simp

lemma compressedSwap_apply {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ)
    (p : Fin (2*Q-2+1)) (k : Fin (Q+1)) :
    (compressedSwap hQ).toLinearMap a (p,k) =
      ∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q p.val i j *
        (∑ b : Fin (2*Q-2+1), pairCoefficient Q b.val i k * a (b,j)) := by
  change (pairSpectatorInclusion hQ).transpose.toLinearMap
    ((swap23 Q).toLinearMap ((pairSpectatorInclusion hQ).toLinearMap a)) (p,k) = _
  rw [pairSpectatorInclusion_transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact pairSpectatorInclusion_apply hQ a i k j

lemma pairCoefficient_zero_contract {Q : ℕ} (hQ : 2 ≤ Q)
    (f : Fin (Q+1) → Fin (Q+1) → ℝ) :
    (∑ i : Fin (Q+1), ∑ j : Fin (Q+1), pairCoefficient Q 0 i j * f i j) =
      (f ⟨1,by omega⟩ 0 - f 0 ⟨1,by omega⟩)/Real.sqrt 2 := by
  have hneq : (⟨1,by omega⟩ : Fin (Q+1)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have hc (i j : Fin (Q+1)) : pairCoefficient Q 0 i j =
      (if i=⟨1,by omega⟩ ∧ j=0 then 1/Real.sqrt 2 else 0) +
        (if i=0 ∧ j=⟨1,by omega⟩ then -1/Real.sqrt 2 else 0) := by
    rw [pairCoefficient_zero_formula hQ]
    by_cases h1 : i=⟨1,by omega⟩ ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h1
      simp [hneq]
    · simp [h1]
  simp_rw [hc, add_mul, Finset.sum_add_distrib, ite_and, ite_mul, zero_mul,
    Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma pairSpectatorInclusion_highest {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (i j k : Fin (Q+1)) (hk : k.val ≤ z) :
    (pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z) ((i,j),k) =
      pairCoefficient Q (z-k.val) i j * highestCoefficient (2*Q-2) Q z (z-k.val) := by
  classical
  let p : Fin (2*Q-2+1) := ⟨z-k.val,by omega⟩
  rw [pairSpectatorInclusion_apply]
  calc
    _ = pairCoefficient Q p.val i j * highestTensor (2*Q-2) Q z (p,k) := by
      apply Finset.sum_eq_single p
      · intro q hq hqp
        have hne : q.val+k.val ≠ z := by
          intro hs
          apply hqp
          apply Fin.ext
          dsimp [p]
          omega
        simp [highestTensor, hne]
      · simp
    _ = _ := by simp [p, highestTensor, Nat.sub_add_cancel hk]

theorem swapScalar_coordinate {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    highestCoefficient (2*Q-2) Q z 0 * swapScalar Q z hQ =
      (((pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z)
        ((⟨1,by omega⟩,⟨z,by omega⟩),0)) -
       ((pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z)
        ((0,⟨z,by omega⟩),⟨1,by omega⟩)))/Real.sqrt 2 := by
  have h := congrFun (compressedSwap_eigenvector hQ hz (by omega : 0 ≤ (2*Q-2)+Q-2*z))
    ((0 : Fin (2*Q-2+1)), (⟨z,by omega⟩ : Fin (Q+1)))
  rw [coupledTensor_zero, compressedSwap_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul, highestTensor, Fin.val_zero,
    Nat.zero_add, ite_true] at h
  rw [mul_comm]
  rw [← h, pairCoefficient_zero_contract hQ]
  simp only [pairSpectatorInclusion_apply, highestTensor]

lemma fallingRatio_penultimate {Q a : ℕ} (hQ : 2 ≤ Q) (ha : a+1 ≤ Q) :
    (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) / ((2*Q-2).descFactorial a : ℝ)) =
      fallingRatio Q (a+1) * ((a : ℝ)+1) * (2*(Q : ℝ)-2-a)/(Q : ℝ) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hd : 0 < ((2*Q-2).descFactorial a : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : a ≤ 2*Q-2)
  have hf : 0 < 2*(Q : ℝ)-2-a := by
    have hqa : (a : ℝ)+1 ≤ Q := by exact_mod_cast ha
    have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  unfold fallingRatio
  rw [show Q.descFactorial (a+1) = Q * (Q-1).descFactorial a by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Q)] using
      Nat.succ_descFactorial_succ (Q-1) a]
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub (by omega : a ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
  push_cast
  field_simp
  rw [mul_div_cancel_right₀ _ (by linarith : 2*((Q : ℝ)-1)-a ≠ 0)]

lemma swapScalar_succ {Q a : ℕ} (hQ : 2 ≤ Q) (ha : a+1 ≤ Q) :
    swapScalar Q (a+1) hQ = -(threeBodyGramCoefficient Q (a+1))/2 := by
  have hz : a+1 ≤ min (2*Q-2) Q := by omega
  have hs0 := highestCoefficient_zero_ne hz
  have hf : 0 ≤ fallingRatio Q (a+1) := by unfold fallingRatio; positivity
  have hg : 0 ≤ ((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
      ((2*Q-2).descFactorial a : ℝ) := by positivity
  have ht : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hs := swapScalar_coordinate hQ ha
  rw [pairSpectatorInclusion_highest hQ ha _ _ _ (by simp),
    pairSpectatorInclusion_highest hQ ha _ _ _ (by simp)] at hs
  simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel] at hs
  rw [pairCoefficient_one hQ ha, pairCoefficient_zero_succ hQ ha,
    highestCoefficient_last hz] at hs
  have hp := highestCoefficient_penultimate hz (by omega : 0 < a+1)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hp
  rw [hp, ← fallingRatio] at hs
  simp only [Nat.cast_add, Nat.cast_one] at hs
  have hsqf := Real.sq_sqrt hf
  have hsqg := Real.sq_sqrt hg
  have hsq2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have he : highestCoefficient (2*Q-2) Q (a+1) 0 * swapScalar Q (a+1) hQ =
      highestCoefficient (2*Q-2) Q (a+1) 0 *
        (((-1 : ℝ)^(a+1)* (1-((a : ℝ)+1))*fallingRatio Q (a+1) +
          (-1 : ℝ)^a * (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
            ((2*Q-2).descFactorial a : ℝ)))/2) := by
    rw [hs]
    calc
      _ = highestCoefficient (2*Q-2) Q (a+1) 0 *
          (((-1 : ℝ)^(a+1)* (1-((a : ℝ)+1))*(Real.sqrt (fallingRatio Q (a+1)))^2 +
            (-1 : ℝ)^a * (Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ) /
              ((2*Q-2).descFactorial a : ℝ)))^2)/(Real.sqrt 2)^2) := by ring
      _ = _ := by rw [hsqf, hsqg, hsq2]
  apply (mul_left_cancel₀ hs0) at he
  rw [he, fallingRatio_penultimate hQ ha, threeBodyGramCoefficient]
  push_cast
  rw [pow_succ]
  have hq : (Q : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma pairSpectatorInclusion_highest_eq_zero {Q z : ℕ} (hQ : 2 ≤ Q)
    (i j k : Fin (Q+1)) (hk : z < k.val) :
    (pairSpectatorInclusion hQ).toLinearMap (highestTensor (2*Q-2) Q z) ((i,j),k) = 0 := by
  rw [pairSpectatorInclusion_apply]
  apply Finset.sum_eq_zero
  intro p hp
  simp [highestTensor, show p.val+k.val ≠ z by omega]

@[simp] lemma highestCoefficient_zero_zero (n m : ℕ) : highestCoefficient n m 0 0 = 1 := by
  simp [highestCoefficient, highestNormalization, highestWeight]

lemma swapScalar_zero {Q : ℕ} (hQ : 2 ≤ Q) : swapScalar Q 0 hQ = 1/2 := by
  have h := swapScalar_coordinate hQ (Nat.zero_le Q)
  rw [pairSpectatorInclusion_highest hQ (Nat.zero_le Q) _ _ _ (by simp),
    pairSpectatorInclusion_highest_eq_zero hQ _ _ _ (by simp)] at h
  simp only [Fin.val_zero, Nat.sub_zero, highestCoefficient_zero_zero, mul_one, one_mul,
    Fin.mk_zero, sub_zero] at h
  have hc := pairCoefficient_one hQ (Nat.zero_le Q)
  simp only [Fin.mk_zero] at hc
  rw [hc] at h
  simp only [fallingRatio, Nat.descFactorial_zero, Nat.cast_one, Nat.cast_zero,
    div_one, Real.sqrt_one, sub_zero, mul_one] at h
  rw [h, div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem swapScalar_eq {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    swapScalar Q z hQ = -(threeBodyGramCoefficient Q z)/2 := by
  cases z with
  | zero =>
    rw [swapScalar_zero hQ]
    norm_num [threeBodyGramCoefficient, fallingRatio]
  | succ a => exact swapScalar_succ hQ hz

theorem compressedSwap_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    (compressedSwap hQ).toLinearMap (coupledTensor (2*Q-2) Q z l) =
      (-(threeBodyGramCoefficient Q z)/2) • coupledTensor (2*Q-2) Q z l := by
  rw [compressedSwap_eigenvector hQ hz hl, swapScalar_eq hQ hz]

end LaughlinGap.Spin

end

end OAI
