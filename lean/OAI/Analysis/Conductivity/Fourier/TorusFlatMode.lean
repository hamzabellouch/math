import Mathlib
import OAI.Analysis.Conductivity.Geometry.TorusExponential
import OAI.Analysis.Conductivity.Variational.ScaledSmoothSeries

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology

lemma flat_proj_norm (i : Fin 3) :
    ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

def torusAngular (h : Fin 2 → ℤ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (h 0:ℝ) • ContinuousLinearMap.proj 1 + (h 1:ℝ) • ContinuousLinearMap.proj 2

lemma torusAngular_norm (h : Fin 2 → ℤ) : ‖torusAngular h‖≤torusSize h := by
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul]
  exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) (flat_proj_norm _))
    (mul_le_of_le_one_right (norm_nonneg _) (flat_proj_norm _))

def flatMode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (x : Fin 3 → ℝ) : ℝ :=
  exp (-torusRate s h*x 0) * cos (torusAngular h x)

lemma flatMode_smooth (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (flatMode s h) := by
  unfold flatMode
  fun_prop

lemma axial_exp_iterated_bound (lam : ℝ) (hlam : 0≤lam) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : Fin 3 → ℝ => exp (-lam*y 0)) x‖ ≤ lam^n*exp (-lam*x 0) := by
  let P : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have he : ContDiff ℝ (↑n) (fun t => exp (-lam*t)) := by fun_prop
  change ‖iteratedFDeriv ℝ n ((fun t => exp (-lam*t)) ∘ P) x‖≤_
  rw [P.iteratedFDeriv_comp_right he x le_rfl]
  have hb := (iteratedFDeriv ℝ n (fun t => exp (-lam*t)) (P x)).norm_compContinuousLinearMap_le (fun _ => P)
  apply hb.trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hp : ‖P‖^n≤1 := pow_le_one₀ (norm_nonneg _) (flat_proj_norm 0)
  apply (mul_le_of_le_one_right (norm_nonneg _) hp).trans_eq
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_exp_const_mul]
  simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,abs_of_nonneg hlam,abs_of_pos (exp_pos _)]
  rfl

lemma angular_cos_iterated_bound (h : Fin 2 → ℤ) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => cos (torusAngular h y)) x‖≤(torusSize h)^n := by
  have hh := linear_comp_iterated_bound (torusAngular h) Real.contDiff_cos
    (fun z => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
      (sin_cos_iterated_bound n z).2) x
  apply hh.trans
  rw [one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusAngular_norm h) _

lemma flatMode_iterated_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ)
    (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (flatMode s h) x‖≤
      (torusRate s h+torusSize h)^n*exp (-torusRate s h*x 0) := by
  have he : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 3 → ℝ => exp (-torusRate s h*y 0)) := by fun_prop
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => cos (torusAngular h y)) := by fun_prop
  apply (norm_iteratedFDeriv_mul_le he hc x (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).trans
  calc
    _ ≤ ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*
        ((torusRate s h)^i*exp (-torusRate s h*x 0))*(torusSize h)^(n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (axial_exp_iterated_bound _ (sqrt_nonneg _) i x) (Nat.cast_nonneg _))
        (angular_cos_iterated_bound h (n-i) x) (norm_nonneg _) (by dsimp [torusRate]; positivity)
    _ = _ := by
      rw [add_pow,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma flatMode_derivative_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (n : ℕ) {δ : ℝ} (hδ : 0<δ) :
    Summable (fun h => (torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) := by
  refine ((torusRate_poly_exp_summable hs n hδ).mul_left ((3:ℝ)^n)).of_nonneg_of_le
    (fun h => by dsimp [torusRate,torusSize]; positivity) ?_
  intro h
  have hl := torusRate_lower hs h
  have hlam : 0≤torusRate s h := sqrt_nonneg _
  calc
    _ ≤ (3*torusRate s h)^n*exp (-δ*torusRate s h) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg hlam (torusSize_nonneg h)) (by linarith) _) (exp_nonneg _)
    _ = _ := by rw [mul_pow,mul_assoc]

def flatPhaseMode (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  exp (-torusRate s h*x 0) * cos (torusAngular h x+phase)

lemma flatPhaseMode_smooth (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (flatPhaseMode s h phase) := by
  unfold flatPhaseMode
  fun_prop

lemma angular_phase_iterated_bound (h : Fin 2 → ℤ) (phase : ℝ) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => cos (torusAngular h y+phase)) x‖≤(torusSize h)^n := by
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ => cos (z+phase)) := by fun_prop
  have hh := linear_comp_iterated_bound (torusAngular h) hc
    (fun z => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_comp_add_const]
      using (sin_cos_iterated_bound n (z+phase)).2) x
  apply hh.trans
  rw [one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (torusAngular_norm h) _

lemma flatPhaseMode_iterated_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ)
    (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (flatPhaseMode s h phase) x‖≤
      (torusRate s h+torusSize h)^n*exp (-torusRate s h*x 0) := by
  have he : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Fin 3 → ℝ => exp (-torusRate s h*y 0)) := by fun_prop
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => cos (torusAngular h y+phase)) := by fun_prop
  apply (norm_iteratedFDeriv_mul_le he hc x (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).trans
  calc
    _ ≤ ∑ i∈Finset.range (n+1), (n.choose i:ℝ)*
        ((torusRate s h)^i*exp (-torusRate s h*x 0))*(torusSize h)^(n-i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (axial_exp_iterated_bound _ (sqrt_nonneg _) i x) (Nat.cast_nonneg _))
        (angular_phase_iterated_bound h phase (n-i) x) (norm_nonneg _) (by dsimp [torusRate]; positivity)
    _ = _ := by
      rw [add_pow,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma weighted_phase_iterated_bound {s : Fin 3 → ℝ} {h : Fin 2 → ℤ}
    (phase a : ℝ) (n : ℕ) (x : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun y => a*flatPhaseMode s h phase y) x‖≤
      |a| *((torusRate s h+torusSize h)^n*exp (-torusRate s h*x 0)) := by
  have hh : ContDiffAt ℝ (↑n) (flatPhaseMode s h phase) x :=
    ((contDiff_infty.mp (flatPhaseMode_smooth s h phase)) n).contDiffAt
  change ‖iteratedFDeriv ℝ n (a • flatPhaseMode s h phase) x‖≤_
  rw [iteratedFDeriv_const_smul_apply hh,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (flatPhaseMode_iterated_bound s h phase n x) (abs_nonneg _)

lemma flatPhaseMode_translation (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase T : ℝ)
    (x : Fin 3 → ℝ) :
    flatPhaseMode s h phase (x+![T,0,0]) = exp (-torusRate s h*T)*flatPhaseMode s h phase x := by
  simp only [flatPhaseMode,torusAngular,add_apply,
    smul_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    smul_eq_mul,add_zero]
  rw [mul_add,exp_add]
  ring

end ScalarConductivity

end

end OAI
