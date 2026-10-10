import Mathlib
import OAI.Analysis.BoundedHochschild.Haagerup
import OAI.Analysis.BoundedHochschild.HarmonicSums

namespace OAI

/-! Catalan functionals, cutoff decay and positive tracial moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCatalan
open Polynomial
noncomputable section

lemma catalan_ratio (n : ℕ) :
    ((n:ℝ)+2) * catalan (n+1) = (4*n+2) * catalan n := by
  have h₁ := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1),
    ← succ_mul_catalan_eq_centralBinom n] at h₁
  have h₂ : (n+1) * ((n+2)*catalan (n+1)) =
      (n+1) * ((4*n+2)*catalan n) := by nlinarith [h₁]
  have h₃ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n+1) h₂
  exact_mod_cast h₃

def catalanDifferential : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (X*(C 4-X))).comp derivative +
    LinearMap.mulLeft ℝ (C 2-C 2*X)

lemma catalanDifferential_apply (p : ℝ[X]) :
    catalanDifferential p = X*(C 4-X)*derivative p + (C 2-C 2*X)*p := rfl

lemma catalanDifferential_X_pow (n : ℕ) :
    catalanDifferential (X^n) = (4*(n:ℝ)+2) • X^n - ((n:ℝ)+2) • X^(n+1) := by
  cases n with
  | zero => simp [catalanDifferential_apply, smul_eq_C_mul]
  | succ n =>
    simp only [catalanDifferential_apply, derivative_X_pow, Nat.add_sub_cancel,
      smul_eq_C_mul, Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat]
    simp only [pow_succ]
    ring

 

lemma differential_moment_zero (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ n, L (X^n) = catalan n) (p : ℝ[X]) :
    L (catalanDifferential p) = 0 := by
  have h (n : ℕ) : L (catalanDifferential (X^n)) = 0 := by
    rw [catalanDifferential_X_pow, map_sub, map_smul, map_smul, hL, hL]
    simpa only [smul_eq_mul, sub_eq_zero] using (catalan_ratio n).symm
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, map_smul, h, smul_zero]

def cutoff : ℝ[X] := 1 - C (1/4) * X

lemma catalanDifferential_cutoff_pow (n : ℕ) :
    catalanDifferential (cutoff ^ n) =
      (4*(n:ℝ)+8) • cutoff^(n+1) - (4*(n:ℝ)+6) • cutoff^n := by
  have h : (4:ℝ[X]) * C (1/4:ℝ) = 1 := by
    rw [← map_ofNat C 4, ← map_mul]; norm_num
  cases n with
  | zero =>
    simp [catalanDifferential_apply, cutoff, smul_eq_C_mul]
    simp only [map_ofNat]
    simp only [one_div] at h
    linear_combination 2*X*h
  | succ n =>
    simp only [catalanDifferential_apply, derivative_pow, Nat.add_sub_cancel,
      smul_eq_C_mul, Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat]
    simp only [cutoff, derivative_sub, derivative_one, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, zero_sub]
    simp only [pow_succ]
    norm_num
    linear_combination ((1-X*C (1/4:ℝ))^n *
      (2*X-X^2*((n:ℝ[X])+3)*C (1/4:ℝ)))*h

lemma cutoff_recurrence (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ n, L (X^n) = catalan n)
    (n : ℕ) :
    (2*(n:ℝ)+4)* L (cutoff^(n+1)) = (2*(n:ℝ)+3)* L (cutoff^n) := by
  have h := differential_moment_zero L hL (cutoff^n)
  rw [catalanDifferential_cutoff_pow, map_sub, map_smul, map_smul] at h
  simp only [smul_eq_mul] at h
  linarith

 
lemma cutoff_moment_sq_le (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ n, L (X^n) = catalan n)
    (n : ℕ) : ((n:ℝ)+2) * (L (cutoff^n))^2 ≤ 2 := by
  induction n with
  | zero =>
    have h := hL 0
    simp only [pow_zero, catalan_zero, Nat.cast_one] at h
    simp [h]
  | succ n ih =>
    have hrec := cutoff_recurrence L hL n
    have hsq : (2*(n:ℝ)+4)^2 * (L (cutoff^(n+1)))^2 =
        (2*(n:ℝ)+3)^2 * (L (cutoff^n))^2 := by
      exact (_root_.mul_pow _ _ 2).symm.trans
        ((congrArg (fun x : ℝ => x^2) hrec).trans (_root_.mul_pow _ _ 2))
    have hc : ((n:ℝ)+3)*(2*(n:ℝ)+3)^2 ≤ ((n:ℝ)+2)*(2*(n:ℝ)+4)^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : 0 < (2*(n:ℝ)+4)^2 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ = ((n:ℝ)+3)*((2*(n:ℝ)+4)^2 * (L (cutoff^(n+1)))^2) := by ring
      _ = ((n:ℝ)+3)*((2*(n:ℝ)+3)^2 * (L (cutoff^n))^2) := by rw [hsq]
      _ ≤ (((n:ℝ)+2)*(2*(n:ℝ)+4)^2) * (L (cutoff^n))^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (L (cutoff^n)))]
      _ = (2*(n:ℝ)+4)^2 * (((n:ℝ)+2) * (L (cutoff^n))^2) := by ring
      _ ≤ (2*(n:ℝ)+4)^2 * 2 := mul_le_mul_of_nonneg_left ih hp.le

open Filter Topology in
 

theorem cutoff_moment_tendsto_zero (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ n, L (X^n) = catalan n) :
    Tendsto (fun n => L (cutoff^n)) atTop (𝓝 0) := by
  have hb (n : ℕ) : (L (cutoff^n))^2 ≤ 2/((n:ℝ)+2) := by
    exact (le_div_iff₀ (by positivity : 0 < (n:ℝ)+2)).mpr
      (by simpa only [mul_comm] using cutoff_moment_sq_le L hL n)
  have hsq : Tendsto (fun n => L (cutoff^n)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hb
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hsq.sqrt

section Trace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
open HochschildRigidity

 
def momentFunctional (a : A) : ℝ[X] →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((τ.toLinearMap.restrictScalars ℝ).comp (aeval a).toLinearMap)

omit [StarOrderedRing A] in
lemma momentFunctional_apply (a : A) (p : ℝ[X]) :
    momentFunctional τ a p = (τ (aeval a p)).re := rfl

omit [StarOrderedRing A] in
lemma momentFunctional_X_pow (a : A) (n : ℕ) :
    momentFunctional τ a (X^n) = (τ (a^n)).re := by
  rw [momentFunctional_apply, aeval_X_pow]

omit [PartialOrder A] [StarOrderedRing A] in
lemma aeval_cutoff (a : A) : aeval a cutoff = 1 - (1/4:ℝ) • a := by
  simp [cutoff, Algebra.smul_def]

omit [StarOrderedRing A] in
open Filter Topology in
lemma cutoff_trace_tendsto_zero (a : A) (hm : ∀ n, (τ (a^n)).re = catalan n) :
    Tendsto (fun n => (τ ((1 - (1/4:ℝ) • a)^n)).re) atTop (𝓝 0) := by
  have h := cutoff_moment_tendsto_zero (momentFunctional τ a)
    (fun n => by rw [momentFunctional_X_pow, hm])
  simpa only [momentFunctional_apply, map_pow, aeval_cutoff] using h

open Filter Topology in
lemma cutoff_preGNS_tendsto_zero (a : A) (ha : IsSelfAdjoint a)
    (hm : ∀ n, (τ (a^n)).re = catalan n) :
    Tendsto (fun n => ‖τ.toPreGNS ((1 - (1/4:ℝ) • a)^n)‖) atTop (𝓝 0) := by
  have hb : IsSelfAdjoint (1 - (1/4:ℝ) • a) :=
    (IsSelfAdjoint.one A).sub ((IsSelfAdjoint.all _).smul ha)
  have hs (n : ℕ) : ‖τ.toPreGNS ((1 - (1/4:ℝ) • a)^n)‖^2 =
      (τ ((1 - (1/4:ℝ) • a)^(2*n))).re := by
    have h := congrArg Complex.re (τ.preGNS_norm_sq
      (τ.toPreGNS ((1 - (1/4:ℝ) • a)^n)))
    simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, star_pow, hb.star_eq,
      ← pow_add, ← Complex.ofReal_pow, Complex.ofReal_re, two_mul] using h
  have ht : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hc := (cutoff_trace_tendsto_zero τ a hm).comp ht
  simp only [Function.comp_def, ← hs] at hc
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hc.sqrt

open Filter Topology in
 

theorem eq_zero_of_mul_eq_zero_of_catalan (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) (a : A) (ha : IsSelfAdjoint a)
    (hm : ∀ n, (τ (a^n)).re = catalan n) (e : A) (he : a*e = 0) : e = 0 := by
  have hb : (1 - (1/4:ℝ) • a)*e = e := by
    rw [sub_mul, one_mul, smul_mul_assoc, he, smul_zero, sub_zero]
  have hbpow (n : ℕ) : (1 - (1/4:ℝ) • a)^n * e = e := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, ih, hb]
  have hn (n : ℕ) : ‖τ.toPreGNS e‖ ≤
      ‖e‖ * ‖τ.toPreGNS ((1 - (1/4:ℝ) • a)^n)‖ := by
    nth_rw 1 [← hbpow n]
    exact preGNS_norm_mul_right_le τ htr _ _
  have ht := (cutoff_preGNS_tendsto_zero τ a ha hm).const_mul ‖e‖
  simp only [mul_zero] at ht
  have hz : ‖τ.toPreGNS e‖ = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (norm_nonneg _)
  exact (preGNS_norm_eq_zero_iff τ hf e).mp hz

end Trace

end
end HochschildCatalan
end

end OAI
