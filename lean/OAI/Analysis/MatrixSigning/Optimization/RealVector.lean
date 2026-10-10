import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Pencil
import OAI.Analysis.MatrixSigning.Arithmetic.ExactStepDecrease

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

noncomputable def realVector (y : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (y i : ℝ))

def l1 (a : Fin n → ℚ) : ℚ := ∑ i, |a i|

def roundScalar (ρ x : ℚ) : ℚ := ρ * ⌊x/ρ⌋

def roundVector (ρ : ℚ) (y : Fin n → ℚ) : Fin n → ℚ := fun i => roundScalar ρ (y i)

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ ∑ i, |v i| := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |v i|) (fun i _ => abs_nonneg _)

lemma l1_bounds (a : Fin n → ℚ) :
    ‖realVector a‖ ≤ (l1 a : ℝ) ∧ (l1 a : ℝ) ≤ (n+1 : ℝ)*‖realVector a‖ := by
  have hcast : (l1 a : ℝ) = ∑ i, |realVector a i| := by
    simp [l1,realVector,Rat.cast_sum]
  rw [hcast]
  refine ⟨norm_le_sum_abs _,?_⟩
  calc
    _ ≤ ∑ _i : Fin n, ‖realVector a‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (realVector a) i))
    _ = (n : ℝ)*‖realVector a‖ := by simp
    _ ≤ _ := by nlinarith [norm_nonneg (realVector a)]

lemma l1_pos {a : Fin n → ℚ} (ha : a ≠ 0) : 0 < l1 a := by
  have ha' : realVector a ≠ 0 := by
    intro h
    apply ha
    funext i
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
    simp only [realVector,PiLp.toLp_apply,PiLp.zero_apply,Rat.cast_eq_zero] at hh
    exact hh
  have hp := norm_pos_iff.mpr ha'
  exact_mod_cast lt_of_lt_of_le hp (l1_bounds a).1

lemma roundScalar_error (ρ x : ℚ) (hρ : 0 < ρ) : |roundScalar ρ x-x| ≤ ρ := by
  have h₁ := Int.floor_le (x/ρ)
  have h₂ := Int.lt_floor_add_one (x/ρ)
  have hlow : roundScalar ρ x ≤ x := by
    dsimp [roundScalar]
    have := mul_le_mul_of_nonneg_left h₁ hρ.le
    rwa [mul_div_cancel₀ _ hρ.ne'] at this
  have hhigh : x < roundScalar ρ x+ρ := by
    dsimp [roundScalar]
    have := mul_lt_mul_of_pos_left h₂ hρ
    rw [mul_div_cancel₀ _ hρ.ne'] at this
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

lemma realVector_round_error (ρ : ℚ) (hρ : 0 < ρ) (y : Fin n → ℚ) :
    ‖realVector (roundVector ρ y)-realVector y‖ ≤ (n+1 : ℝ)*(ρ : ℝ) := by
  calc
    _ ≤ ∑ i, |(realVector (roundVector ρ y)-realVector y) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin n, (ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := roundScalar_error ρ (y i) hρ
      simpa only [realVector,roundVector,PiLp.sub_apply,PiLp.toLp_apply,Rat.cast_sub,
        Rat.cast_abs] using (Rat.cast_le (K := ℝ)).mpr h
    _ = (n : ℝ)*(ρ : ℝ) := by simp
    _ ≤ _ := by
      have hp : 0 < (ρ : ℝ) := by exact_mod_cast hρ
      nlinarith

noncomputable def normalized (a : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  (-(l1 a : ℝ)⁻¹) • realVector a

lemma normalized_norm_le_one (a : Fin n → ℚ) : ‖normalized a‖ ≤ 1 := by
  by_cases ha : a=0
  · simp [normalized,l1,ha,realVector]
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hq]
  exact (inv_mul_le_iff₀ hq).mpr (by simpa only [mul_one] using (l1_bounds a).1)

lemma normalized_margin (K : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (y a : Fin n → ℚ) {r : ℝ} (hr : 0 ≤ r) (ha : a ≠ 0)
    (hball : Metric.closedBall c r ⊆ K)
    (hsep : ∀ z ∈ K, inner ℝ (realVector a) (z-realVector y) ≤ 0) :
    r/(n+1) ≤ inner ℝ (normalized a) (c-realVector y) := by
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  have ha0 : realVector a ≠ 0 := by
    intro h
    have han := (l1_bounds a).2
    rw [h,norm_zero,mul_zero] at han
    linarith
  have hnorm : 0 < ‖realVector a‖ := norm_pos_iff.mpr ha0
  let v := (-‖realVector a‖⁻¹) • realVector a
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
  have hsep' : ∀ z ∈ K, inner ℝ v (realVector y) ≤ inner ℝ v z := by
    intro z hz
    have hh := hsep z hz
    rw [inner_sub_right] at hh
    dsimp [v]
    rw [real_inner_smul_left,real_inner_smul_left]
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr (inv_nonneg.mpr hnorm.le))
  have hm := CurrentKS.RationalOptimization.separating_margin K c (realVector y) v hr hball hv hsep' le_rfl
  have hn : normalized a = (‖realVector a‖/(l1 a : ℝ)) • v := by
    dsimp [normalized,v]
    rw [smul_smul]
    congr 1
    field_simp
  rw [hn,real_inner_smul_left]
  have hrn : (1 : ℝ)/(n+1) ≤ ‖realVector a‖/(l1 a : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<n+1) hq).mpr
    simpa only [one_mul,mul_comm] using (l1_bounds a).2
  calc
    r/(n+1) = ((1:ℝ)/(n+1))*r := by ring
    _ ≤ (‖realVector a‖/(l1 a : ℝ))*inner ℝ v (c-realVector y) :=
      mul_le_mul hrn hm hr (div_nonneg hnorm.le hq.le)

def Pencil.next (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ) : Fin n → ℚ :=
  match B.witness y with
  | none => y
  | some v => roundVector mesh (fun i => y i-step*B.normal v i/l1 (B.normal v))

lemma realVector_step (y a : Fin n → ℚ) (step : ℚ) :
    realVector (fun i => y i-step*a i/l1 a) = realVector y+(step : ℝ) • normalized a := by
  ext i
  simp [realVector,normalized,Rat.cast_sub,Rat.cast_mul,div_eq_mul_inv]
  ring

end CurrentKS.RationalSDP

end OAI
