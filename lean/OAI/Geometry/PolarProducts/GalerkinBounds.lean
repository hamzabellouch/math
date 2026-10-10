import OAI.Geometry.PolarProducts.QuadraticAction

namespace OAI

universe u113

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 def leftCoeff (a : Coeff (ι ⊕ ν) κ) : Coeff ι κ :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm (fun p => a (Sum.inl p.1,p.2))

 def rightCoeff (a : Coeff (ι ⊕ ν) κ) : Coeff ν κ :=
  (EuclideanSpace.equiv (ν × κ) ℂ).symm (fun p => a (Sum.inr p.1,p.2))

 def joinCoeff (a : Coeff ι κ) (b : Coeff ν κ) : Coeff (ι ⊕ ν) κ :=
  (EuclideanSpace.equiv ((ι ⊕ ν) × κ) ℂ).symm (fun p => Sum.elim
    (fun i => a (i,p.2)) (fun j => b (j,p.2)) p.1)

omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem leftCoeff_apply (a : Coeff (ι ⊕ ν) κ) (p : ι × κ) :
    leftCoeff a p = a (Sum.inl p.1,p.2) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem rightCoeff_apply (a : Coeff (ι ⊕ ν) κ) (p : ν × κ) :
    rightCoeff a p = a (Sum.inr p.1,p.2) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem joinCoeff_inl (a : Coeff ι κ) (b : Coeff ν κ) (i : ι) (j : κ) :
    joinCoeff a b (Sum.inl i,j) = a (i,j) := rfl
omit [Fintype ι] [Fintype ν] [Fintype κ] in
@[simp] theorem joinCoeff_inr (a : Coeff ι κ) (b : Coeff ν κ) (i : ν) (j : κ) :
    joinCoeff a b (Sum.inr i,j) = b (i,j) := rfl

 theorem norm_joinCoeff_sq (a : Coeff ι κ) (b : Coeff ν κ) :
    ‖joinCoeff a b‖^2 = ‖a‖^2+‖b‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_sum_type,
    joinCoeff_inl, joinCoeff_inr]

 theorem energy_joinCoeff (w : (ι ⊕ ν) × κ → ℝ) (a : Coeff ι κ) (b : Coeff ν κ) :
    energy w (joinCoeff a b) = energy (fun p => w (Sum.inl p.1,p.2)) a +
      energy (fun p => w (Sum.inr p.1,p.2)) b := by
  simp only [energy, Fintype.sum_prod_type, Fintype.sum_sum_type,
    joinCoeff_inl, joinCoeff_inr]

 theorem loop_joinCoeff (k : ι → ℤ) (l : ν → ℤ) (a : Coeff ι κ) (b : Coeff ν κ) :
    loop (Sum.elim k l) (joinCoeff a b) = loop k a + loop l b := by
  ext t j
  simp only [ContinuousMap.add_apply, PiLp.add_apply, loop_coord, eval,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, joinCoeff_inl, joinCoeff_inr]

 def splitEquiv (d : ν → ℝ) (hd : ∀ i, d i ≠ 0) :
    Coeff (ι ⊕ ν) κ ≃L[ℝ] Coeff ι κ × Coeff ν κ :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun a => (leftCoeff a, diag (fun p => d p.1) (rightCoeff a))
    invFun := fun p => joinCoeff p.1 (diag (fun q => (d q.1)⁻¹) p.2)
    left_inv := by
      intro a
      ext ⟨i,j⟩
      cases i with
      | inl i => rfl
      | inr i => simp [hd i]
    right_inv := by
      intro ⟨a,b⟩
      ext p
      · rfl
      · simp [hd p.1]
    map_add' := by
      intro a b
      ext p
      · rfl
      · simp [smul_add]
    map_smul' := by
      intro r a
      ext p
      · rfl
      · simp
        ring }

 theorem splitEquiv_symm (d : ν → ℝ) (hd : ∀ i, d i ≠ 0)
    (a : Coeff ι κ) (b : Coeff ν κ) :
    (splitEquiv d hd).symm (a,b) = joinCoeff a (diag (fun q => (d q.1)⁻¹) b) := rfl

 def positiveScale (k : ν → ℕ) (hk : ∀ i, 0 < k i) :
    Coeff (ι ⊕ ν) κ ≃L[ℝ] Coeff ι κ × Coeff ν κ :=
  splitEquiv (fun i => Real.sqrt (k i : ℝ)) (fun i =>
    (Real.sqrt_pos.2 (by exact_mod_cast hk i)).ne')

 theorem energy_scaled (k : ν → ℕ) (hk : ∀ i, 0 < k i) (b : Coeff ν κ) :
    energy (fun p => (k p.1 : ℝ))
      (diag (fun p => (Real.sqrt (k p.1 : ℝ))⁻¹) b) = ‖b‖^2 := by
  classical
  simp only [energy, EuclideanSpace.norm_sq_eq]
  apply sum_congr rfl
  intro p _
  have hp : 0 < (k p.1 : ℝ) := by exact_mod_cast hk p.1
  rw [diag_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt hp.le]
  field_simp

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem action_positive_lower (k : ι → ℤ) (l : ν → ℕ)
    (hl : Function.Injective l) (hl0 : ∀ i, 0 < l i)
    {H : Vector κ → ℝ} (hH : Continuous H) {C : ℝ} (hC : 0 ≤ C)
    (hup : ∀ z, H z ≤ C*‖z‖^4) (b : Coeff ν κ) :
    Real.pi*‖b‖^2-C*(Fintype.card κ : ℝ)*‖b‖^4 ≤
      action (Sum.elim k (fun i => (l i : ℤ))) H ((positiveScale l hl0).symm (0,b)) := by
  let v := diag (fun p : ν × κ => (Real.sqrt (l p.1 : ℝ))⁻¹) b
  have hkin : energy (fun p : (ι ⊕ ν) × κ =>
      Real.pi*((Sum.elim k (fun i => (l i : ℤ)) p.1 : ℤ) : ℝ)) (joinCoeff 0 v) = Real.pi*‖b‖^2 := by
    rw [energy_joinCoeff]
    simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast]
    have hz : energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) 0 = 0 := by simp [energy]
    rw [hz, zero_add, energy_mul, energy_scaled l hl0]
  have hp := potential_upper_fourth l hl hl0 hH hC hup v
  change _ ≤ C*(Fintype.card κ : ℝ)*(energy (fun p : ν × κ => (l p.1 : ℝ)) v)^2 at hp
  rw [energy_scaled l hl0] at hp
  have hlo : potential (Sum.elim k (fun i => (l i : ℤ))) H (joinCoeff 0 v) =
      potential (fun i => (l i : ℤ)) H v := by
    unfold potential
    rw [loop_joinCoeff, loop_zero, zero_add]
  change _ ≤ energy _ (joinCoeff 0 v)-potential _ H (joinCoeff 0 v)
  rw [hkin, hlo]
  nlinarith

 theorem cone_scaled_single [DecidableEq ν] [DecidableEq κ]
    (l : ν → ℕ) (hl0 : ∀ i, 0 < l i) (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    (a : Coeff ι κ) (s : ℝ) :
    (positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ)) =
      joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)) := by
  apply congrArg (joinCoeff a)
  ext p
  simp only [diag_apply, PiLp.smul_apply, PiLp.single_apply]
  split_ifs with hp
  · subst p
    simp [hl1]
  · simp

 theorem action_cone_upper [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ) (hl0 : ∀ i, 0 < l i)
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : ∀ z, 0 ≤ H z) (a : Coeff ι κ) (s : ℝ) :
    action (Sum.elim k (fun i => (l i : ℤ))) H
      ((positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ))) ≤ Real.pi*s^2 := by
  rw [cone_scaled_single l hl0 i₀ hl1 j₀]
  have hn := energy_nonpos (fun p : ι × κ => Real.pi*(k p.1 : ℝ))
    (fun p => mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by exact_mod_cast hk0 p.1)) a
  have hp := potential_nonneg (Sum.elim k (fun i => (l i : ℤ))) hH
    (joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)))
  unfold action
  rw [energy_joinCoeff]
  simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast, energy_smul,
    energy_single, hl1, Nat.cast_one, norm_one, one_pow, mul_one]
  nlinarith

 theorem action_cone_far [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ) (hl0 : ∀ i, 0 < l i)
    (hkl : Function.Injective (Sum.elim k (fun i => (l i : ℤ))))
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : Continuous H) (d : κ → ℝ) (C η : ℝ)
    (hd : ∀ j, η ≤ d j) (hd0 : Real.pi+η ≤ d j₀)
    (hlo : ∀ z, energy d z-C ≤ H z) (a : Coeff ι κ) (s : ℝ) :
    action (Sum.elim k (fun i => (l i : ℤ))) H
      ((positiveScale l hl0).symm (a,s • PiLp.single 2 (i₀,j₀) (1 : ℂ))) ≤
      C-η*(‖a‖^2+s^2) := by
  rw [cone_scaled_single l hl0 i₀ hl1 j₀]
  have hn := energy_nonpos (fun p : ι × κ => Real.pi*(k p.1 : ℝ))
    (fun p => mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (by exact_mod_cast hk0 p.1)) a
  have hdlo := energy_lower (fun p : ι × κ => d p.2) η (fun p => hd p.2) a
  have hp := potential_lower (Sum.elim k (fun i => (l i : ℤ))) hkl hH d C hlo
    (joinCoeff a (s • PiLp.single 2 (i₀,j₀) (1 : ℂ)))
  unfold action
  rw [energy_joinCoeff]
  rw [energy_joinCoeff] at hp
  simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast, energy_smul,
    energy_single, hl1, Nat.cast_one, norm_one, one_pow, mul_one] at hp ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hd0) (sq_nonneg s)]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 def velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) : Coeff ι κ :=
   Complex.I • ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a)

omit [Fintype ι] [Fintype κ] in
 theorem mode_velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) (i : ι) :
    mode (velocityCoeff k a) i = (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ)) • mode a i := by
  ext j
  simp only [mode_apply, velocityCoeff, PiLp.smul_apply, diag_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  simp only [map_mul, map_intCast, map_ofNat]
  change Complex.I * ((2 : ℂ) * (((Real.pi : ℂ)*(k i : ℂ))*a (i,j))) =
    (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ))*a (i,j)
  ring

 theorem hasDerivAt_loop (k : ι → ℤ) (a : Coeff ι κ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => loop k a (s : Time)) (loop k (velocityCoeff k a) (t : Time)) t := by
  have hs := HasDerivAt.fun_sum (u := univ) (fun i _ =>
    (hasDerivAt_fourier (1 : ℝ) (k i) t).smul_const (mode a i))
  change HasDerivAt (fun s : ℝ => loop k a (s : Time)) _ t at hs
  apply hs.congr_deriv
  simp only [loop_apply, mode_velocityCoeff, smul_smul, div_one, Complex.ofReal_one]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

 theorem norm_velocityCoeff_critical (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) (ha : gradient (action k H) a = 0) :
    ‖velocityCoeff k a‖ = ‖project k (gradLoop k hH a)‖ := by
  rw [gradient_action k hH, sub_eq_zero] at ha
  simp only [velocityCoeff, ha, norm_smul, Complex.norm_I, one_mul]

 theorem norm_project_grad (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hd : ∀ j, |d j| ≤ D)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ) :
    ‖project k (gradLoop k hH a)‖ ≤ B+2*D*‖a‖ := by
  have hb : ‖project k (remainderLoop k hH d a)‖ ≤ B :=
    project_bounded k hk _ hB (fun t => by rw [remainderLoop_apply]; exact hrem _)
  have he : project k (gradLoop k hH a) = project k (remainderLoop k hH d a) +
      (2 : ℝ) • diag (fun p => d p.2) a := by
    rw [remainderLoop, project_sub, project_loop k hk]
    abel
  have hn := norm_add_le (project k (remainderLoop k hH d a))
    ((2 : ℝ) • diag (fun p => d p.2) a)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)] at hn
  have hdiag := norm_diag_upper (fun p : ι × κ => d p.2) hD (fun p => hd p.2) a
  nlinarith

 theorem intervalIntegral_eq_average {E : Type u113} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Time → E) : (∫ t in (0:ℝ)..1, f (t : Time)) = ∫ t : Time, f t ∂μ := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [zero_add, inv_one, one_smul] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f

 def meanAction {H : Vector κ → ℝ} (_hH : ContDiff ℝ ∞ H) (x : C(Time,Vector κ)) : ℝ :=
    ∫ t : Time, inner (𝕜 := ℝ) (gradient H (x t)) (x t)/2-H (x t) ∂μ

 theorem contDiff_meanAction {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (meanAction hH) := by
  have hg : ContDiff ℝ ∞ (fun z : Vector κ => inner (𝕜 := ℝ) (gradient H z) z/2-H z) :=
    (((contDiff_gradient_function hH).inner ℝ contDiff_id).div_const 2).sub hH
  exact average.contDiff.comp (SmoothPaths.contDiff_superpose hg)

 theorem critical_action_eq (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) (ha : gradient (action k H) a = 0) :
    action k H a = meanAction hH (loop k a) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  have hi := integral_inner_loop k (gradLoop k hH a) a
  rw [← he, real_inner_smul_left, ← energy_eq_inner] at hi
  have hgi : Integrable (fun t : Time => inner (𝕜 := ℝ) (gradient H (loop k a t)) (loop k a t)) μ :=
    integrable_continuous ((gradLoop k hH a).continuous.inner (loop k a).continuous)
  have hpi : Integrable (fun t : Time => H (loop k a t)) μ :=
    integrable_continuous (hH.continuous.comp (loop k a).continuous)
  unfold meanAction
  rw [integral_sub (hgi.div_const 2) hpi, integral_div]
  change action k H a = (∫ t : Time, inner (𝕜 := ℝ) (gradLoop k hH a t) (loop k a t) ∂μ)/2-potential k H a
  rw [hi]
  unfold action
  ring

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 def linkRadius (κ : Type) [Fintype κ] (M : ℝ) : ℝ :=
  Real.sqrt (Real.pi/(2*(M*(Fintype.card κ : ℝ)+1)))

 def linkLevel (κ : Type) [Fintype κ] (M : ℝ) : ℝ :=
  Real.pi/4*(linkRadius κ M)^2

 theorem linkRadius_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkRadius κ M := by
  unfold linkRadius
  apply Real.sqrt_pos.2
  exact div_pos Real.pi_pos (by positivity)

 theorem linkRadius_sq {M : ℝ} (hM : 0 ≤ M) :
    (linkRadius κ M)^2 = Real.pi/(2*(M*(Fintype.card κ : ℝ)+1)) :=
  Real.sq_sqrt (by positivity)

 theorem linkLevel_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkLevel κ M := by
  unfold linkLevel
  exact mul_pos (div_pos Real.pi_pos (by norm_num)) (sq_pos_of_pos (linkRadius_pos hM))

 theorem linkLevel_bound {M : ℝ} (hM : 0 ≤ M) :
    2*linkLevel κ M ≤ Real.pi*(linkRadius κ M)^2-
      M*(Fintype.card κ : ℝ)*(linkRadius κ M)^4 := by
  have hden : 0 < 2*(M*(Fintype.card κ : ℝ)+1) := by positivity
  have he : 2*(M*(Fintype.card κ : ℝ)+1)*(linkRadius κ M)^2 = Real.pi := by
    rw [linkRadius_sq hM]
    field_simp
  have hr : 0 ≤ (linkRadius κ M)^2 := sq_nonneg _
  have hm : M*(Fintype.card κ : ℝ)*(linkRadius κ M)^2 ≤ Real.pi/2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hm hr
  unfold linkLevel
  nlinarith

 theorem exists_link_epsilon {a : ℝ} (ha : 0 < a) :
    ∃ ε > 0, ∀ s : ℝ, 0 < s → s < ε → Real.pi*s^2 ≤ a/2 := by
  let ε := Real.sqrt (a/(2*Real.pi))
  have hε : 0 < ε := Real.sqrt_pos.2 (div_pos ha (by positivity))
  have hεsq : ε^2 = a/(2*Real.pi) := Real.sq_sqrt (by positivity)
  refine ⟨ε,hε,fun s hs hse => ?_⟩
  have hs2 : s^2 ≤ ε^2 := pow_le_pow_left₀ hs.le hse.le 2
  have hm := mul_le_mul_of_nonneg_left hs2 Real.pi_pos.le
  rw [hεsq] at hm
  have hid : Real.pi*(a/(2*Real.pi)) = a/2 := by field_simp
  rwa [hid] at hm

 theorem exists_link_far {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (C : ℝ) :
    ∃ R : ℝ, ρ < R ∧ ∀ u s : ℝ, 0 ≤ u → R ≤ max u |s| → C-η*(u^2+s^2) ≤ 0 := by
  let R := max (ρ+1) (max 1 ((|C|+1)/η))
  have hR : ρ < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRc : (|C|+1)/η ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hReq : |C|+1 ≤ η*R := by
    have := (div_le_iff₀ hη).mp hRc
    linarith
  refine ⟨R,hR,fun u s _ hfar => ?_⟩
  have hsq : R^2 ≤ u^2+s^2 := by
    rcases le_max_iff.mp hfar with hy | hss
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hy 2
      nlinarith [sq_nonneg s]
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hss 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg u]
  have hh : R ≤ R^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (hh.trans hsq) hη.le
  linarith [le_abs_self C]
 theorem finite_critical [DecidableEq ν] [DecidableEq κ]
    (k : ι → ℤ) (hk0 : ∀ i, k i ≤ 0) (l : ν → ℕ)
    (hl : Function.Injective l) (hl0 : ∀ i, 0 < l i)
    (hkl : Function.Injective (Sum.elim k (fun i => (l i : ℤ))))
    (i₀ : ν) (hl1 : l i₀ = 1) (j₀ : κ)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (hH0 : ∀ z, 0 ≤ H z)
    (d₀ d : κ → ℝ) {C M η γ B : ℝ}
    (hM : 0 ≤ M) (hη : 0 < η) (hγ : 0 < γ) (hB : 0 ≤ B)
    (hup : ∀ z, H z ≤ M*‖z‖^4)
    (hd : ∀ j, η ≤ d₀ j) (hd0 : Real.pi+η ≤ d₀ j₀)
    (hlo : ∀ z, energy d₀ z-C ≤ H z)
    (hgap : ∀ i j, γ ≤ |Real.pi*((Sum.elim k (fun i => (l i : ℤ)) i : ℤ) : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ x : Coeff (ι ⊕ ν) κ,
      linkLevel κ M ≤ action (Sum.elim k (fun i => (l i : ℤ))) H x ∧
      action (Sum.elim k (fun i => (l i : ℤ))) H x ≤ max C (linkLevel κ M) ∧
      gradient (action (Sum.elim k (fun i => (l i : ℤ))) H) x = 0 := by
  have ha : 0 < linkLevel κ M := linkLevel_pos hM
  have hρ : 0 < linkRadius κ M := linkRadius_pos hM
  obtain ⟨ε,hε,hnear⟩ := exists_link_epsilon ha
  obtain ⟨R,hR,hfar⟩ := exists_link_far hρ hη C
  let e : Coeff ν κ := PiLp.single 2 (i₀,j₀) (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  apply FiniteLinking.exists_critical
    (H := Coeff (ι ⊕ ν) κ) (E := Coeff ι κ) (F := Coeff ν κ)
    (Φ := action (Sum.elim k (fun i => (l i : ℤ))) H)
    (positiveScale l hl0) (contDiff_action (Sum.elim k (fun i => (l i : ℤ))) hH) he ha
    (le_max_right _ _) hρ hε hR
  ·
    intro z hz
    have hb := action_positive_lower k l hl hl0 hH.continuous hM hup z
    rw [hz] at hb
    exact (linkLevel_bound hM).trans hb
  ·
    intro y s hs hse
    exact (action_cone_upper k hk0 l hl0 i₀ hl1 j₀ hH0 y s).trans (hnear s hs hse)
  ·
    intro y s _ hys
    have hs := hfar ‖y‖ s (norm_nonneg y) (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hys)
    exact (action_cone_far k hk0 l hl0 hkl i₀ hl1 j₀ hH.continuous d₀ C η hd hd0 hlo y s).trans
      (hs.trans (by positivity))
  ·
    intro y s _ _
    have hnon : 0 ≤ η*(‖y‖^2+s^2) := mul_nonneg hη.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact (action_cone_far k hk0 l hl0 hkl i₀ hl1 j₀ hH.continuous d₀ C η hd hd0 hlo y s).trans
      ((sub_le_self C hnon).trans (le_max_left _ _))
  ·
    exact gradient_coercive _ hkl hH d hγ hB hgap hrem

end
end FourierPolynomial

end NonsqueezingInline

end OAI
