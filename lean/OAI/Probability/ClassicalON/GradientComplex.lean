import OAI.Probability.ClassicalON.FamilyAlgebra

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def normObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => ‖f σ‖, f.continuous.norm⟩

def reObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => (f σ).re, Complex.continuous_re.comp f.continuous⟩

def imObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => (f σ).im, Complex.continuous_im.comp f.continuous⟩

theorem averageLinear_nonneg [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.averageLinear f :=
  S.average_nonneg hf

theorem averageLinear_mono [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) (hfg : ∀ σ, f σ ≤ g σ) :
    S.averageLinear f ≤ S.averageLinear g := S.average_mono f.continuous g.continuous hfg

theorem averageLinear_mul_self_nonneg [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) : 0 ≤ S.averageLinear (f*f) :=
  S.averageLinear_nonneg _ (fun σ => mul_self_nonneg (f σ))

theorem averageLinear_cauchySchwarz [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) :
    (S.averageLinear (f*g))^2 ≤ S.averageLinear (f*f) * S.averageLinear (g*g) := by
  have hp (t : ℝ) : 0 ≤ S.averageLinear (f*f) * (t*t) +
      (2*S.averageLinear (f*g))*t + S.averageLinear (g*g) := by
    have h := S.averageLinear_mul_self_nonneg (t • f + g)
    have he : (t • f + g)*(t • f + g) =
        (t*t) • (f*f) + (2*t) • (f*g) + g*g := by
      ext σ
      simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [he, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    nlinarith
  have h := discrim_le_zero hp
  unfold discrim at h
  nlinarith

theorem averageLinear_mul_le_sqrt [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) :
    S.averageLinear (f*g) ≤
      Real.sqrt (S.averageLinear (f*f)) * Real.sqrt (S.averageLinear (g*g)) := by
  rw [← Real.sqrt_mul (S.averageLinear_mul_self_nonneg f)]
  exact Real.le_sqrt_of_sq_le (S.averageLinear_cauchySchwarz f g)

theorem norm_averageComplex_le [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    ‖S.averageComplexLinear f‖ ≤ S.averageLinear (normObservable f) := by
  change ‖(∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.Z_pos _)]
  calc _ ≤ (∫ σ, ‖f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)‖ ∂S.reference) /
      S.Z (fun _ => 1) :=
      div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) (S.Z_pos _).le
    _ = S.averageLinear (normObservable f) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rfl

omit [Fintype V] in
@[simp] theorem complexEnergy_re (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    (S.complexEnergy M u σ).re = S.energy (fun e => (u e).re • M) σ := by
  rw [S.energy_weighted]
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_re]

omit [Fintype V] in
@[simp] theorem complexEnergy_im (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    (S.complexEnergy M u σ).im = S.energy (fun e => (u e).im • M) σ := by
  rw [S.energy_weighted]
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_im]

omit [Fintype V] in
@[simp] theorem complexEnergy_conj (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℂ) (σ : V → Spin n) :
    S.complexEnergy M (fun e => conj (u e)) σ = conj (S.complexEnergy M u σ) := by
  simp [complexEnergy, MixedAlgebra.weighted]

theorem complex_gradient_current_bound [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : M ∈ skewAdjoint (SpinOperator n)) (hMn : ‖M‖ ≤ 1)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => ‖S.complexEnergy M (S.differential f) σ‖^2) ≤
      β * ∑ e, ‖S.differential f e‖^2 := by
  have hr := S.gradient_current_bound β hb M hM hMn (fun x => (f x).re)
    (fun x s hs => by rw [hP x s hs, Complex.zero_re])
  have hi := S.gradient_current_bound β hb M hM hMn (fun x => (f x).im)
    (fun x s hs => by rw [hP x s hs, Complex.zero_im])
  have he (σ : V → Spin n) : ‖S.complexEnergy M (S.differential f) σ‖^2 =
      (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2 +
      (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, complexEnergy_re, complexEnergy_im]
    simp only [differential, Complex.sub_re, Complex.sub_im, pow_two]
    rfl
  have he' : (fun σ => ‖S.complexEnergy M (S.differential f) σ‖^2) =
      (fun σ => (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2) +
      (fun σ => (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2) := funext he
  rw [he', S.average_add
    (f := fun σ => (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2)
    (g := fun σ => (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2)
    ((S.continuous_energy _).pow 2) ((S.continuous_energy _).pow 2)]
  have hn : (∑ e, ‖S.differential f e‖^2) =
      (∑ e, ((f (S.right e)).re - (f (S.left e)).re)^2) +
      (∑ e, ((f (S.right e)).im - (f (S.left e)).im)^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, differential, pow_two]
  rw [hn, mul_add]
  exact add_le_add hr hi

theorem averageComplex_re [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    (S.averageComplexLinear f).re = S.averageLinear (reObservable f) := by
  change ((∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  have h := integral_re (S.integrable_complex_integrand f.continuous)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rfl

theorem averageComplex_conj [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    S.averageComplexLinear ⟨fun σ => conj (f σ), Complex.continuous_conj.comp f.continuous⟩ =
      conj (S.averageComplexLinear f) := by
  change (∫ σ, conj (f σ) * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ) =
      conj ((∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
        (S.Z (fun _ => 1) : ℂ))
  conv_lhs => arg 1; arg 2; ext σ; rw [← Complex.conj_ofReal (Real.exp _), ← map_mul]
  rw [integral_conj, map_div₀]
  congr 1
  exact (Complex.conj_ofReal _).symm

omit [Fintype V] [Fintype E] in
theorem abs_localCoefficient_le (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : ‖M‖ ≤ 1) (σ : V → Spin n) (e : E) :
    |S.localCoefficient M σ e| ≤ β := by
  have hi : |⟪(σ (S.left e)).val, M (σ (S.right e)).val⟫_ℝ| ≤ 1 := by
    calc _ ≤ ‖(σ (S.left e)).val‖ * ‖M (σ (S.right e)).val‖ := abs_real_inner_le_norm _ _
         _ ≤ ‖(σ (S.left e)).val‖ * (‖M‖ * ‖(σ (S.right e)).val‖) :=
           mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
         _ = ‖M‖ := by simp
         _ ≤ 1 := hM
  rw [localCoefficient, abs_mul, abs_of_nonneg (hb e).1]
  exact (mul_le_of_le_one_right (hb e).1 hi).trans (hb e).2

end ClassicalON.SpinSystem

namespace ClassicalON

theorem norm_square_le_one {n : ℕ} (M : SpinOperator n) (hM : ‖M‖ ≤ 1) : ‖M^2‖ ≤ 1 := by
  calc ‖M^2‖ ≤ ‖M‖ * ‖M‖ := by simpa only [pow_two] using norm_mul_le M M
       _ ≤ 1 * 1 := mul_le_mul hM hM (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

theorem mixedAB_norm_le : ‖mixedAB‖ ≤ 1 := by
  have he : mixedAB = (1/2 : ℝ) • (axisA*axisB+axisB*axisA) := by
    have h := congrArg matrixOperator mixedMatrixAB_sym
    simpa only [map_smul, map_add, map_mul, mixedAB, axisA, axisB] using h
  rw [he, norm_smul]
  have hab := (norm_mul_le axisA axisB).trans
    (mul_le_mul axisA_norm_le axisB_norm_le (norm_nonneg _) zero_le_one)
  have hba := (norm_mul_le axisB axisA).trans
    (mul_le_mul axisB_norm_le axisA_norm_le (norm_nonneg _) zero_le_one)
  have hsum := norm_add_le (axisA*axisB) (axisB*axisA)
  norm_num at hab hba ⊢
  linarith

theorem mixedAAB_norm_le : ‖mixedAAB‖ ≤ 1 := by
  have he : mixedAAB = (-1/3 : ℝ) • axisB := by
    simp only [mixedAAB, mixedMatrixAAB, map_smul, axisB]
  rw [he, norm_smul]
  norm_num
  linarith [axisB_norm_le]

theorem mixedABB_norm_le : ‖mixedABB‖ ≤ 1 := by
  have he : mixedABB = (-1/3 : ℝ) • axisA := by
    simp only [mixedABB, mixedMatrixABB, map_smul, axisA]
  rw [he, norm_smul]
  norm_num
  linarith [axisA_norm_le]

theorem mixedAABB_norm_le : ‖mixedAABB‖ ≤ 1 := by
  have he : mixedAABB = (-1/6 : ℝ) • (axisA^2+axisB^2) := by
    simp only [mixedAABB, mixedMatrixAABB, map_smul, map_add, map_pow, axisA, axisB]
  rw [he, norm_smul]
  have hsum := norm_add_le (axisA^2) (axisB^2)
  have ha := norm_square_le_one axisA axisA_norm_le
  have hb := norm_square_le_one axisB axisB_norm_le
  norm_num
  linarith

end ClassicalON

end

end OAI
