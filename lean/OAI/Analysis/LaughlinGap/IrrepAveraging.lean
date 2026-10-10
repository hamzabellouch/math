import Mathlib
import OAI.Analysis.LaughlinGap.SpinAveraging

namespace OAI

/-! Irrep Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

lemma standardLadderSystem_casimir (n : ℕ) (x : Fin (n+1) → ℝ) :
    (standardLadderSystem n).casimir x = ((n : ℝ)*(n+2)) • x := by
  funext p
  simp only [LadderSystem.casimir_apply, standardLadderSystem, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, weight_apply, lowering_raising_apply]
  ring

theorem standardLadderMap_eq_zero {n m : ℕ} (hnm : n ≠ m)
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem m)) :
    A.toLinearMap = 0 := by
  apply LinearMap.ext
  intro x
  have h := A.casimir x
  rw [standardLadderSystem_casimir, standardLadderSystem_casimir, map_smul] at h
  have hne : (m : ℝ)*(m+2) ≠ (n : ℝ)*(n+2) := by
    intro he
    exact hnm (spinCasimir_injective he).symm
  funext j
  have he := congrFun h j
  change (m : ℝ)*(m+2)*A.toLinearMap x j = (n : ℝ)*(n+2)*A.toLinearMap x j at he
  exact (mul_left_cancel₀ (sub_ne_zero.mpr hne) (by nlinarith :
    ((m : ℝ)*(m+2)-(n : ℝ)*(n+2)) * A.toLinearMap x j =
      ((m : ℝ)*(m+2)-(n : ℝ)*(n+2))*0))

lemma ladderStep_pos (n : ℕ) (p : Fin n) : 0 < ladderStep n p := by
  apply Real.sqrt_pos.mpr
  have hp : (p.val : ℝ) < n := by exact_mod_cast p.isLt
  exact mul_pos (by positivity) (by linarith)

lemma weight_single (n : ℕ) (i : Fin (n+1)) :
    weight n (Pi.single i 1) = ((n : ℝ)-2*i.val) • Pi.single i 1 := by
  funext j
  by_cases h : i=j
  · subst j; simp
  · simp [h, eq_comm]

lemma lowering_single (n : ℕ) (p : Fin n) :
    lowering n (Pi.single p.castSucc 1) = ladderStep n p • Pi.single p.succ 1 := by
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
    by_cases h : j=p
    · subst j; simp
    · have hn : p.val ≠ j.val := by intro hp; apply h; exact (Fin.ext hp).symm
      simp [Fin.ext_iff, hn, eq_comm]

theorem standardLadderMap_schur {n : ℕ}
    (A : LadderMap (standardLadderSystem n) (standardLadderSystem n)) (x : Fin (n+1) → ℝ) :
    A.toLinearMap x = A.toLinearMap (Pi.single 0 1) 0 • x := by
  let c : Fin (n+1) → ℝ := fun i => A.toLinearMap (Pi.single i 1) i
  have hd (i : Fin (n+1)) : A.toLinearMap (Pi.single i 1) = c i • Pi.single i 1 := by
    have hw := A.weight (Pi.single i 1)
    change weight n (A.toLinearMap (Pi.single i 1)) = A.toLinearMap (weight n _) at hw
    rw [weight_single, map_smul] at hw
    funext j
    by_cases h : i=j
    · subst j; simp [c]
    · have hv : i.val ≠ j.val := by exact fun he => h (Fin.ext he)
      have he := congrFun hw j
      simp only [weight_apply, Pi.smul_apply, smul_eq_mul] at he
      have hne : ((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val) ≠ 0 := by
        intro he
        apply hv
        exact_mod_cast (by linarith : (i.val : ℝ)=j.val)
      have hz : A.toLinearMap (Pi.single i 1) j = 0 := by
        apply (mul_eq_zero.mp (show (((n : ℝ)-2*j.val)-((n : ℝ)-2*i.val)) *
          A.toLinearMap (Pi.single i 1) j = 0 by nlinarith)).resolve_left hne
      simp [hz, h, eq_comm]
  have hc : ∀ i, c i = c 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have he := A.lower (Pi.single i.castSucc 1)
      change lowering n (A.toLinearMap (Pi.single i.castSucc 1)) = A.toLinearMap (lowering n _) at he
      rw [hd, map_smul, lowering_single, map_smul, hd] at he
      have hh := congrFun he i.succ
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hh
      have hci : c i.succ = c i.castSucc := by
        nlinarith [ladderStep_pos n i]
      exact hci.trans ih
  rw [A.toLinearMap.pi_apply_eq_sum_univ x]
  have hs (i : Fin (n+1)) : (fun j => if i=j then (1:ℝ) else 0) = Pi.single i 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  simp only [hs, hd, hc, smul_smul]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Pi.smul_apply, c, mul_comm]

theorem standardSpin_average (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    average (rotationCommutant (loweringMatrix (standardLadderSystem n))) A =
      (A.trace / (n+1 : ℕ)) • 1 := by
  let S := rotationCommutant (loweringMatrix (standardLadderSystem n))
  let Y := average S A
  let L := commutantLadderMap (standardLadderSystem n) (average_mem S A)
  let c := L.toLinearMap (Pi.single 0 1) 0
  have he : Y = c • 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hv := standardLadderMap_schur L x
    change Matrix.toLin' Y x = c • x at hv
    rwa [Matrix.toLin'_apply] at hv
  have hc : c = A.trace / (n+1 : ℕ) := by
    have ht := average_trace S A
    change Y.trace = A.trace at ht
    rw [he, Matrix.trace_smul, Matrix.trace_one] at ht
    apply (eq_div_iff (by positivity : ((n+1 : ℕ) : ℝ) ≠ 0)).mpr
    simpa using ht
  exact he.trans (congrArg (fun t : ℝ => t • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) hc)

end LaughlinGap.Spin

end

end OAI
