import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalMode

namespace OAI

/-! Uniform fourth-order bounds for the actual normalized transverse
Gaussian. Polynomial Gaussian moments bound each explicit derivative. -/

noncomputable section
namespace ContinuumCoulomb

theorem power_exponential_bound (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t^k*Real.exp (-a*t) ≤ (k.factorial:ℝ)/a^k := by
  have hf : 0 < (k.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have he := Real.pow_div_factorial_le_exp (a*t) (mul_nonneg ha.le ht) k
  have hid : ((a*t)^k/(k.factorial:ℝ))*((k.factorial:ℝ)/a^k) = t^k := by
    rw [mul_pow]
    field_simp
  have hb := mul_le_mul_of_nonneg_right he (show 0 ≤ (k.factorial:ℝ)/a^k by positivity)
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-a*t)).le
  have hc : (Real.exp (a*t)*((k.factorial:ℝ)/a^k))*Real.exp (-a*t) = (k.factorial:ℝ)/a^k := by
    rw [mul_right_comm,← Real.exp_add]
    simp
  exact hb'.trans_eq hc

theorem verticalMode_monomial_bound {freq : ℝ} (hfreq : 0 < freq) (k : ℕ) (z : ℝ) :
    |z|^k*‖verticalMode freq z‖ ≤
      (1+(k.factorial:ℝ)/(freq/2)^k)/Real.sqrt (Real.sqrt (Real.pi/freq)) := by
  have hd : 0 < Real.sqrt (Real.sqrt (Real.pi/freq)) := by positivity
  have hp : |z|^k ≤ 1+z^(2*k) := by
    by_cases hz : |z| ≤ 1
    · have ht := pow_le_pow_left₀ (abs_nonneg z) hz k
      simp only [one_pow] at ht
      linarith [pow_nonneg (sq_nonneg z) k,show z^(2*k) = (z^2)^k by rw [pow_mul]]
    · have ht := pow_le_pow_right₀ (le_of_not_ge hz) (show k ≤ 2*k by omega)
      rw [pow_mul,sq_abs,← pow_mul] at ht
      linarith
  have hg := power_exponential_bound k (show 0 < freq/2 by positivity) (sq_nonneg z)
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(freq/2)*z^2)).le
  have he : Real.exp (-(freq/2)*z^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  have hb : |z|^k*Real.exp (-(freq/2)*z^2) ≤ 1+(k.factorial:ℝ)/(freq/2)^k := by
    rw [add_mul,one_mul] at hh
    rw [← pow_mul] at hg
    linarith
  rw [Real.norm_of_nonneg (verticalMode_positive hfreq z).le,verticalMode]
  have harg : -freq*z^2/2 = -(freq/2)*z^2 := by ring
  rw [harg,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hb hd.le

theorem verticalMode_third_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (deriv (verticalMode freq)))
      ((3*freq^2*z-freq^3*z^3)*verticalMode freq z) z := by
  rw [show deriv (deriv (verticalMode freq)) =
    (fun x => (freq^2*x^2-freq)*verticalMode freq x) from funext (verticalMode_second_deriv freq)]
  convert (((((hasDerivAt_id z).pow 2).const_mul (freq^2)).sub_const freq).mul
    (verticalMode_hasDerivAt freq z)) using 1 <;> (try funext x) <;>
    (simp only [id_eq,Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]; all_goals ring)

theorem verticalMode_third_deriv (freq z : ℝ) :
    deriv (deriv (deriv (verticalMode freq))) z =
      (3*freq^2*z-freq^3*z^3)*verticalMode freq z :=
  (verticalMode_third_hasDerivAt freq z).deriv

theorem verticalMode_fourth_hasDerivAt (freq z : ℝ) :
    HasDerivAt (deriv (deriv (deriv (verticalMode freq))))
      ((3*freq^2-6*freq^3*z^2+freq^4*z^4)*verticalMode freq z) z := by
  rw [show deriv (deriv (deriv (verticalMode freq))) =
    (fun x => (3*freq^2*x-freq^3*x^3)*verticalMode freq x) from funext (verticalMode_third_deriv freq)]
  convert ((((hasDerivAt_id z).const_mul (3*freq^2)).sub
    (((hasDerivAt_id z).pow 3).const_mul (freq^3))).mul
    (verticalMode_hasDerivAt freq z)) using 1 <;> (try funext x) <;>
    (simp only [id_eq,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,mul_one]; all_goals ring)

theorem verticalMode_fourth_deriv (freq z : ℝ) :
    deriv (deriv (deriv (deriv (verticalMode freq)))) z =
      (3*freq^2-6*freq^3*z^2+freq^4*z^4)*verticalMode freq z :=
  (verticalMode_fourth_hasDerivAt freq z).deriv

private def verticalHermiteCoeffs (freq : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![1,0,0,0,0],![0,-freq,0,0,0],![-freq,0,freq^2,0,0],
    ![0,3*freq^2,0,-freq^3,0],![3*freq^2,0,-6*freq^3,0,freq^4]]

private theorem verticalMode_iteratedDeriv (freq z : ℝ) (k : Fin 5) :
    iteratedDeriv k.val (verticalMode freq) z =
      (∑ j : Fin 5, verticalHermiteCoeffs freq k j*z^(j:ℕ))*verticalMode freq z := by
  fin_cases k <;>
    simp [verticalHermiteCoeffs,Fin.sum_univ_succ,iteratedDeriv_succ,iteratedDeriv_zero,
      verticalMode_deriv,verticalMode_second_deriv,verticalMode_third_deriv,verticalMode_fourth_deriv] <;> ring_nf <;> simp

theorem vertical_mode_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ z,
      ‖iteratedFDeriv ℝ k (verticalMode freq) z‖ ≤ B := by
  let P (k : Fin 5) : ℝ :=
    (1+(k.val.factorial:ℝ)/(freq/2)^k.val)/Real.sqrt (Real.sqrt (Real.pi/freq))
  have hP (k : Fin 5) : 0 ≤ P k := by dsimp [P]; positivity
  let M := ∑ k : Fin 5, P k
  have hM : 0 ≤ M := Finset.sum_nonneg (fun k _ => hP k)
  let A (k : Fin 5) : ℝ := ∑ j : Fin 5, |verticalHermiteCoeffs freq k j|
  have hA (k : Fin 5) : 0 ≤ A k := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let B := M*(∑ k : Fin 5, A k)+1
  have hB : 1 ≤ B := by
    dsimp [B]
    have hs : 0 ≤ ∑ k : Fin 5, A k := Finset.sum_nonneg (fun k _ => hA k)
    nlinarith [mul_nonneg hM hs]
  refine ⟨B,hB,fun k hk z => ?_⟩
  let i : Fin 5 := ⟨k,by omega⟩
  have hm (j : Fin 5) : |z|^(j:ℕ)*‖verticalMode freq z‖ ≤ M :=
    (verticalMode_monomial_bound hfreq j.val z).trans
      (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ j))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i.val (verticalMode freq) z‖ ≤ B
  rw [verticalMode_iteratedDeriv,norm_mul]
  calc
    _ ≤ (∑ j : Fin 5, ‖verticalHermiteCoeffs freq i j*z^(j:ℕ)‖)*‖verticalMode freq z‖ :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)
    _ = ∑ j : Fin 5, |verticalHermiteCoeffs freq i j| *(|z|^(j:ℕ)*‖verticalMode freq z‖) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs,mul_assoc]
    _ ≤ ∑ j : Fin 5, |verticalHermiteCoeffs freq i j| *M :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hm j) (abs_nonneg _))
    _ = A i*M := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j : Fin 5, A j)*M :=
      mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)) hM
    _ ≤ B := by dsimp [B]; nlinarith

end ContinuumCoulomb

end

end OAI
