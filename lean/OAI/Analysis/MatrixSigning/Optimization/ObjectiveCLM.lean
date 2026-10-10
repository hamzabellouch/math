import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ConvexInnerBall
import OAI.Analysis.MatrixSigning.Optimization.Level

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.realEval_convex (B : Pencil n m) (x y : Fin n → ℝ) (a b : ℝ)
    (hab : a+b=1) : B.realEval (a • x+b • y) = a • B.realEval x+b • B.realEval y := by
  ext i j
  simp only [Pencil.realEval,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Pi.add_apply,Pi.smul_apply]
  simp only [mul_add,Finset.mul_sum,add_mul,mul_assoc]
  rw [Finset.sum_add_distrib]
  have h := congrArg (fun t : ℝ => t * (B.constant.map (fun q : ℚ => (q : ℝ)) i j)) hab
  nlinarith [h]

lemma Pencil.convex_feasible (B : Pencil n m) : Convex ℝ B.feasible := by
  intro x hx y hy a b ha hb hab
  change (B.realEval (a • x+b • y)).PosSemidef
  rw [B.realEval_convex x y a b hab]
  exact (hx.smul ha).add (hy.smul hb)

def objectiveCLM (f : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  innerSL ℝ (realVector f)

lemma objectiveCLM_apply (f : Fin n → ℚ) (y : EuclideanSpace ℝ (Fin n)) :
    objectiveCLM f y = (fun i => (f i:ℝ)) ⬝ᵥ y := by
  change (∑ i, y i * (f i:ℝ)) = ∑ i, (f i:ℝ)*y i
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma norm_convexCombination_le (z c : EuclideanSpace ℝ (Fin n)) {a R : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖(1-a) • z+a • c‖ ≤ R := by
  calc
    _ ≤ ‖(1-a) • z‖+‖a • c‖ := norm_add_le _ _
    _ = (1-a)*‖z‖+a*‖c‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg ha,abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a)*R+a*R := add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ha1))
      (mul_le_mul_of_nonneg_left hc ha)
    _ = R := by ring

def nearRadius (δ L R r : ℚ) : ℚ := δ/(L*(2*R+r))*r

def optimizeFuel (δ U : ℚ) : ℕ := ⌈2*U/δ⌉₊+3

lemma nearRadius_pos {δ L R r : ℚ} (hδ : 0 < δ) (hL : 0 < L)
    (hR : 0 ≤ R) (hr : 0 < r) : 0 < nearRadius δ L R r := by
  unfold nearRadius
  positivity

lemma nearRadius_le {δ L R r : ℚ} (hL : 0 < L) (hR : 0 ≤ R) (hr : 0 < r)
    (hδsmall : δ ≤ L*(2*R+r)) : nearRadius δ L R r ≤ r := by
  have hd : (0:ℚ) < L*(2*R+r) := by positivity
  exact (mul_le_mul_of_nonneg_right ((div_le_one hd).mpr hδsmall) hr.le).trans_eq (one_mul r)

lemma exists_near_level {δ U v : ℝ} (hδ : 0 < δ) (hv : -U ≤ v) (hvU : v ≤ U) :
    ∃ k : ℕ, k ≤ ⌈2*U/δ⌉₊+3 ∧ v+δ ≤ -U+k*δ ∧ -U+k*δ ≤ v+2*δ := by
  let k : ℕ := ⌈(v+U)/δ⌉₊+1
  have hratio : 0 ≤ (v+U)/δ := div_nonneg (by linarith) hδ.le
  have hc := Nat.le_ceil ((v+U)/δ)
  have hlt := Nat.ceil_lt_add_one hratio
  refine ⟨k,?_,?_,?_⟩
  · have hm : (v+U)/δ ≤ 2*U/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
    have hh := Nat.ceil_mono hm
    dsimp [k]
    omega
  · have hh := (div_le_iff₀ hδ).mp hc
    dsimp [k]
    push_cast
    nlinarith
  · have hh := (lt_div_iff₀ hδ).mp (show (⌈(v+U)/δ⌉₊:ℝ) < (v+U+δ)/δ by
        convert hlt using 1
        first | rfl | field_simp)
    dsimp [k]
    push_cast
    linarith

theorem Pencil.optimize_nearOptimal (B : Pencil n m) (f : Fin n → ℚ)
    (δ L R r U : ℚ) (z c : EuclideanSpace ℝ (Fin n))
    (hδ : 0 < δ) (hL : 0 < L) (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ‖objectiveCLM f‖ ≤ (L:ℝ)) (hzK : z ∈ B.feasible)
    (hz : ‖z‖ ≤ (R:ℝ)) (hc : ‖c‖ ≤ (R:ℝ))
    (hball : Metric.closedBall c (r:ℝ) ⊆ B.feasible)
    (hδsmall : δ ≤ L*(2*R+r))
    (hu : -(U:ℝ) ≤ objectiveCLM f z ∧ objectiveCLM f z ≤ (U:ℝ)) :
    let y := B.optimize f δ (nearRadius δ L R r) R U (optimizeFuel δ U)
    realVector y ∈ B.feasible ∧ objectiveCLM f (realVector y) ≤ objectiveCLM f z+2*(δ:ℝ) := by
  let a : ℝ := (δ:ℝ)/((L:ℝ)*(2*(R:ℝ)+(r:ℝ)))
  have hden : 0 < (L:ℝ)*(2*(R:ℝ)+(r:ℝ)) := by
    exact_mod_cast (show (0:ℚ) < L*(2*R+r) by positivity)
  have ha : 0 < a := div_pos (by exact_mod_cast hδ) hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (by exact_mod_cast hδsmall)
  have hb := CurrentKS.RationalOptimization.nearOptimal_innerBall B.feasible B.convex_feasible
    (objectiveCLM f) z c (δ := (δ:ℝ)) hzK hf (by exact_mod_cast hL) (by exact_mod_cast hR)
    (by exact_mod_cast hr) hz hc hball (by exact_mod_cast hδ) (by exact_mod_cast hδsmall)
  obtain ⟨k,hk,hlo,hhi⟩ := exists_near_level (δ := (δ:ℝ)) (by exact_mod_cast hδ) hu.1 hu.2
  have hkr : k ≤ optimizeFuel δ U := by
    have hb : (2*(U:ℝ)/(δ:ℝ)) ≤ (⌈2*U/δ⌉₊:ℝ) := by
      exact_mod_cast (Nat.le_ceil (2*U/δ))
    exact hk.trans (Nat.add_le_add_right (Nat.ceil_le.mpr hb) 3)
  have he : (nearRadius δ L R r : ℝ)=a*(r:ℝ) := by
    simp only [nearRadius,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,a]
  have hcle : ‖(1-a) • z+a • c‖ ≤ (R:ℝ) := norm_convexCombination_le _ _ ha.le ha1 hz hc
  have haccept := B.levelCandidate_accepts f δ (nearRadius δ L R r) R U k
    ((1-a) • z+a • c) (nearRadius_pos hδ hL hR hr)
    ((nearRadius_le hL hR hr hδsmall).trans hr1) hR hcle (by
      rw [he]
      intro y hy
      have hy' := hb hy
      refine ⟨hy'.1,?_⟩
      change (fun i => (f i:ℝ)) ⬝ᵥ y ≤ (level δ U k:ℝ)
      rw [← objectiveCLM_apply]
      have hl : (level δ U k:ℝ)= -(U:ℝ)+(k:ℝ)*(δ:ℝ) := by simp [level]
      rw [hl]
      exact hy'.2.trans hlo)
  have hout := B.optimize_bound f δ (nearRadius δ L R r) R U hδ.le hkr haccept
  refine ⟨hout.1,?_⟩
  rw [objectiveCLM_apply]
  apply hout.2.trans
  simpa only [level,Rat.cast_add,Rat.cast_neg,Rat.cast_mul,Rat.cast_natCast] using hhi

end
end CurrentKS.RationalSDP

end OAI
