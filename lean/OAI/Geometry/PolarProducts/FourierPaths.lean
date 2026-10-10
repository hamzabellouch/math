import OAI.Geometry.PolarProducts.FourierIntegrals

namespace OAI

universe u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
 theorem real_inner_eq_complex_re {α : Type u100} [Fintype α] (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = RCLike.re (inner (𝕜 := ℂ) a b) := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner, map_sum]

variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

abbrev Vector (κ : Type u103) := EuclideanSpace ℂ κ
abbrev Coeff (ι : Type u104) (κ : Type u105) := EuclideanSpace ℂ (ι × κ)

def mode (a : Coeff ι κ) (i : ι) : Vector κ :=
  (EuclideanSpace.equiv κ ℂ).symm (fun j => a (i,j))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem mode_apply (a : Coeff ι κ) (i : ι) (j : κ) : mode a i j = a (i,j) := rfl

def loop (k : ι → ℤ) (a : Coeff ι κ) : C(Time, Vector κ) where
  toFun t := ∑ i, fourier (k i) t • mode a i
  continuous_toFun := continuous_finsetSum _ (fun i _ =>
    (fourier (k i)).continuous.smul continuous_const)

@[simp] theorem loop_apply (k : ι → ℤ) (a : Coeff ι κ) (t : Time) :
    loop k a t = ∑ i, fourier (k i) t • mode a i := rfl

 theorem loop_coord (k : ι → ℤ) (a : Coeff ι κ) (t : Time) (j : κ) :
    loop k a t j = eval k (fun i => a (i,j)) t := by
  simp [loop_apply, eval, mul_comm]

 def loopCLM (k : ι → ℤ) : Coeff ι κ →L[ℝ] C(Time, Vector κ) :=
  LinearMap.toContinuousLinearMap {
    toFun := loop k
    map_add' := by
      intro a b
      ext t j
      simp only [ContinuousMap.add_apply, PiLp.add_apply, loop_coord, eval,
        add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      ext t j
      simp only [ContinuousMap.smul_apply, PiLp.smul_apply, loop_coord, eval,
        RingHom.id_apply, RCLike.real_smul_eq_coe_mul, mul_assoc, ← Finset.mul_sum] }

@[simp] theorem loopCLM_apply (k : ι → ℤ) (a : Coeff ι κ) : loopCLM k a = loop k a := rfl

 theorem integral_loop_norm_sq (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop k a t‖^2 ∂μ) = ‖a‖^2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq, loop_coord]
  rw [integral_finsetSum]
  · simp_rw [integral_norm_sq k hk]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  · intro j _
    exact integrable_continuous ((continuous_eval k _).norm.pow 2)

 theorem integral_loop_coord_sq (k : ι → ℤ) (hk : Function.Injective k)
    (a : Coeff ι κ) (j : κ) :
    (∫ t : Time, ‖loop k a t j‖^2 ∂μ) = ∑ i, ‖a (i,j)‖^2 := by
  simp_rw [loop_coord]
  exact integral_norm_sq k hk _

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u106} {κ : Type u107} [Fintype ι] [Fintype κ]

 theorem vector_norm_fourth_le (z : Vector κ) :
    ‖z‖^4 ≤ (Fintype.card κ : ℝ) * ∑ j, ‖z j‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset κ)
    (fun j => ‖z j‖^2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, ← pow_mul] at h
  calc
    _ = (∑ j, ‖z j‖^2)^2 := by rw [← EuclideanSpace.norm_sq_eq]; ring
    _ ≤ _ := by simpa only [mul_comm] using h

 theorem integral_loop_norm_fourth_le (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (Fintype.card κ : ℝ) * (∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  classical
  let L := loop (fun i => (k i : ℤ)) a
  have hcont : Continuous (fun t : Time => (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4) :=
    continuous_const.mul (continuous_finsetSum _ (fun j _ =>
      (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)))
  calc
    _ ≤ ∫ t : Time, (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4 ∂μ :=
      integral_mono (integrable_continuous (L.continuous.norm.pow 4))
        (integrable_continuous hcont) (fun t => vector_norm_fourth_le (L t))
    _ = (Fintype.card κ : ℝ)*∑ j, ∫ t : Time, ‖L t j‖^4 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      intro j _
      exact integrable_continuous (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)
    _ ≤ (Fintype.card κ : ℝ)*∑ j, (∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      simp only [L, loop_coord]
      exact positive_L4 k hk hk0 _
    _ ≤ (Fintype.card κ : ℝ)*(∑ j, ∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ =>
        Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = _ := by rw [Finset.sum_comm, Fintype.sum_prod_type]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

 theorem fourierCoeff_eval (k : ι → ℤ) (a : ι → ℂ) (j : ℤ) :
    fourierCoeff (eval k a) j = ∑ i, if j = k i then a i else 0 := by
  classical
  simp only [fourierCoeff, eval, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have he (t : Time) : fourier (-j) t * (a i * fourier (k i) t) =
        a i*(conj (fourier j t)*fourier (k i) t) := by rw [fourier_neg]; ring
    simp_rw [he]
    rw [integral_const_mul, integral_conj_fourier_mul]
    split_ifs <;> simp only [mul_one, mul_zero]
  · intro i _
    exact integrable_continuous ((fourier (-j)).continuous.mul
      (continuous_const.mul (fourier (k i)).continuous))

 def project (k : ι → ℤ) (f : C(Time, Vector κ)) : Coeff ι κ :=
  (EuclideanSpace.equiv (ι × κ) ℂ).symm (fun p => fourierCoeff (fun t => f t p.2) (k p.1))

omit [Fintype ι] [Fintype κ] in
@[simp] theorem project_apply (k : ι → ℤ) (f : C(Time, Vector κ)) (p : ι × κ) :
    project k f p = fourierCoeff (fun t => f t p.2) (k p.1) := rfl

 theorem project_loop (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    project k (loop k a) = a := by
  classical
  ext p
  simp only [project_apply, loop_coord, fourierCoeff_eval, hk.eq_iff]
  simp

 theorem integral_fourier_mul_conj (k : ℤ) (f : C(Time, ℂ)) :
    (∫ t : Time, conj (f t) * fourier k t ∂μ) = conj (fourierCoeff f k) := by
  rw [fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, map_mul, fourier_neg, starRingEnd_self_apply]
  ring

 theorem integral_inner_loop (k : ι → ℤ) (f : C(Time, Vector κ)) (a : Coeff ι κ) :
    (∫ t : Time, inner (𝕜 := ℝ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℝ) (project k f) a := by
  classical
  have hstage (j : κ) :
      (∫ t : Time, conj (f t j)*eval k (fun i => a (i,j)) t ∂μ) =
        ∑ i, conj (project k f (i,j))*a (i,j) := by
    simp only [eval, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      have he (t : Time) : conj (f t j) * (a (i,j) * fourier (k i) t) =
          (conj (f t j) * fourier (k i) t) * a (i,j) := by ring
      simp_rw [he]
      rw [integral_mul_const]
      exact congrArg (fun z => z*a (i,j))
        (integral_fourier_mul_conj (k i)
          ⟨fun t => f t j, (PiLp.continuous_apply 2 _ j).comp f.continuous⟩)
    · intro i _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_const.mul (fourier (k i)).continuous))
  have hcomplex : (∫ t : Time, inner (𝕜 := ℂ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℂ) (project k f) a := by
    change (∫ t : Time, ∑ j, loop k a t j * conj (f t j) ∂μ) =
      ∑ p : ι × κ, a p * conj (project k f p)
    simp_rw [loop_coord, mul_comm (eval k _ _)]
    rw [integral_finsetSum]
    · simp_rw [hstage]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      congr 1
      ext j
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro j _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_eval k _))
  simp only [real_inner_eq_complex_re]
  rw [integral_re (integrable_continuous
    (show Continuous (fun t => inner (𝕜 := ℂ) (f t) (loop k a t)) from
      f.continuous.inner (loop k a).continuous)), hcomplex]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

 theorem project_bessel (k : ι → ℤ) (hk : Function.Injective k) (f : C(Time, Vector κ)) :
    ‖project k f‖^2 ≤ ∫ t : Time, ‖f t‖^2 ∂μ := by
  let a := project k f
  have hnon : 0 ≤ ∫ t : Time, ‖f t-loop k a t‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have h1 : Integrable (fun t : Time => ‖f t‖^2) μ :=
    integrable_continuous (f.continuous.norm.pow 2)
  have h2 : Integrable (fun t : Time => inner (𝕜 := ℝ) (f t) (loop k a t)) μ :=
    integrable_continuous (f.continuous.inner (loop k a).continuous)
  have h3 : Integrable (fun t : Time => ‖loop k a t‖^2) μ :=
    integrable_continuous ((loop k a).continuous.norm.pow 2)
  simp_rw [norm_sub_sq_real] at hnon
  rw [integral_add, integral_sub, integral_const_mul,
    integral_inner_loop, integral_loop_norm_sq k hk, real_inner_self_eq_norm_sq] at hnon
  rotate_left
  · exact h1
  · exact h2.const_mul 2
  · exact h1.sub (h2.const_mul 2)
  · exact h3
  dsimp [a] at *
  linarith

 theorem project_bounded (k : ι → ℤ) (hk : Function.Injective k)
    (f : C(Time, Vector κ)) {B : ℝ} (hB : 0 ≤ B) (hf : ∀ t, ‖f t‖ ≤ B) :
    ‖project k f‖ ≤ B := by
  have hi : (∫ t : Time, ‖f t‖^2 ∂μ) ≤ B^2 := by
    calc
      _ ≤ ∫ _ : Time, B^2 ∂μ := integral_mono
        (integrable_continuous (f.continuous.norm.pow 2)) (integrable_const _) (fun t =>
          pow_le_pow_left₀ (norm_nonneg _) (hf t) 2)
      _ = _ := by simp
  have h := (project_bessel k hk f).trans hi
  nlinarith [norm_nonneg (project k f)]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]

 def average : C(Time, ℝ) →L[ℝ] ℝ := by
  let L : C(Time, ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun f => ∫ t : Time, f t ∂μ
    map_add' := fun f g => integral_add (integrable_continuous f.continuous)
      (integrable_continuous g.continuous)
    map_smul' := fun r f => by simp only [ContinuousMap.smul_apply,
      integral_smul, RingHom.id_apply] }
  apply L.mkContinuous 1
  intro f
  change ‖∫ t : Time, f t ∂μ‖ ≤ 1*‖f‖
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun t => f.norm_coe_le_norm t))

@[simp] theorem average_apply (f : C(Time, ℝ)) : average f = ∫ t : Time, f t ∂μ := rfl

 def potential (k : ι → ℤ) (H : Vector κ → ℝ) (a : Coeff ι κ) : ℝ :=
  ∫ t : Time, H (loop k a t) ∂μ

 theorem contDiff_potential (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (potential k H) := by
  exact average.contDiff.comp ((SmoothPaths.contDiff_superpose hH).comp (loopCLM k).contDiff)

 theorem contDiff_gradient_function {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (gradient H) :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.contDiff.comp
    (hH.fderiv_right (by simp))

 def gradLoop (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    C(Time, Vector κ) :=
  ⟨fun t => gradient H (loop k a t), (contDiff_gradient_function hH).continuous.comp
    (loop k a).continuous⟩

 theorem hasGradientAt_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    HasGradientAt (potential k H) (project k (gradLoop k hH a)) a := by
  have hl : HasFDerivAt (loop k) (loopCLM k) a := by
    change HasFDerivAt (loopCLM k) (loopCLM k) a
    exact (loopCLM (κ := κ) k).hasFDerivAt (x := a)
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hH.differentiable (by simp)) (hH.fderiv_right (m := ∞) (by simp)).continuous (loop k a)).comp
      a hl
  have hi := average.hasFDerivAt.comp a hS
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (potential k H) _ a at hi
  apply hi.congr_fderiv
  ext b
  change (∫ t : Time, fderiv ℝ H (loop k a t) (loop k b t) ∂μ) =
    inner (𝕜 := ℝ) (project k (gradLoop k hH a)) b
  simp_rw [← inner_gradient_left]
  exact integral_inner_loop k (gradLoop k hH a) b

 theorem gradient_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    gradient (potential k H) a = project k (gradLoop k hH a) :=
  (hasGradientAt_potential k hH a).gradient

end
end FourierPolynomial

end NonsqueezingInline

end OAI
