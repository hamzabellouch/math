import Mathlib
import OAI.Analysis.Crouzeix.ContourHomotopy
import OAI.Analysis.Crouzeix.MatrixContours

namespace OAI

/-! Contour Polynomials. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_pow (Γ : SmoothContour) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t) ^ n) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hder (t : ℝ) : HasDerivAt (fun r : ℝ => (n + 1 : ℂ)⁻¹ * Γ.path r ^ (n + 1))
      (deriv Γ.path t * Γ.path t ^ n) t := by
    have h := ((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.pow (n + 1)).const_mul
      (n + 1 : ℂ)⁻¹
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_comm]
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * Γ.path t ^ n)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (Γ.smooth.continuous.pow n)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hi
  simpa only [Γ.closed, sub_self] using he

theorem smul_resolvent_eq [CompleteSpace H] (A : Operator H) {z : ℂ}
    (hz : z ∉ numericalClosure A) :
    z • Ring.inverse (algebraMap ℂ (Operator H) z - A) =
      1 + A * Ring.inverse (algebraMap ℂ (Operator H) z - A) := by
  have hu : IsUnit (algebraMap ℂ (Operator H) z - A) := by
    change z ∈ resolventSet ℂ A
    by_contra he
    exact hz (spectrum_subset_numericalClosure A he)
  have he := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at he
  exact sub_eq_iff_eq_add.mp he

theorem contourEval_mul_id_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => z * f z) =
      A * contourEval A Γ.toSmoothContour f := by
  let p := fun t : ℝ => f (Γ.path t) • contourKernel A Γ.toSmoothContour t
  let q := fun t : ℝ => deriv Γ.path t * f (Γ.path t)
  let L := ContinuousLinearMap.mul ℂ (Operator H) A
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hp : ContinuousOn p (Icc (0 : ℝ) 1) := hfc.smul (continuousOn_contourKernel A Γ)
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) := Γ.smooth.continuous_deriv_one.continuousOn.mul hfc
  have hip : IntervalIntegrable p MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_contourIntegrand A Γ hf
  have hiL : IntervalIntegrable (fun t => L (p t)) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one, Function.comp_def] using!
      L.continuous.comp_continuousOn hp
  have hiq : IntervalIntegrable (fun t => q t • (1 : Operator H))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using! hq.smul continuousOn_const
  have halg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t =
        q t • (1 : Operator H) + L (p t) := by
    have he := smul_resolvent_eq A (Γ.avoids t ht).2
    have hscalar : Γ.path t * f (Γ.path t) * deriv Γ.path t =
        (deriv Γ.path t * f (Γ.path t)) * Γ.path t := by ring
    dsimp only [contourKernel, p, q, L]
    rw [smul_smul, hscalar, ← smul_smul, he, smul_add]
    congr 1
    simp only [ContinuousLinearMap.mul_apply', mul_smul_comm, smul_smul]
    rw [mul_comm (f (Γ.path t))]
  rw [contourEval_eq_kernel, contourEval_eq_kernel]
  have hi : (∫ t in (0 : ℝ)..1, (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t) =
      L (∫ t in (0 : ℝ)..1, p t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, q t • (1 : Operator H) + L (p t) :=
        intervalIntegral.integral_congr (fun t ht => halg t (by simpa using ht))
      _ = (∫ t in (0 : ℝ)..1, q t) • (1 : Operator H) + L (∫ t in (0 : ℝ)..1, p t) := by
        rw [intervalIntegral.integral_add hiq hiL, intervalIntegral.integral_smul_const,
          L.intervalIntegral_comp_comm hip]
      _ = _ := by rw [show (∫ t in (0 : ℝ)..1, q t) = 0 from hzero, zero_smul, zero_add]
  rw [hi]
  exact (map_smul L _ _).symm

theorem contourEval_pow [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n) = A ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using contourEval_one A Γ
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ
      (continuous_pow n).continuousOn (Γ.toSmoothContour.integral_deriv_mul_pow n)
    simpa only [pow_succ', ih] using he

theorem contourEval_const_mul (A : Operator H) (Γ : SmoothContour) (c : ℂ) (f : ℂ → ℂ) :
    contourEval A Γ (fun z => c * f z) = c • contourEval A Γ f := by
  simp only [contourEval_eq_kernel, mul_smul, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem contourEval_sum [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, contourEval A Γ.toSmoothContour (f i) := by
  simp only [contourEval_eq_kernel, Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum (fun i hi => intervalIntegrable_contourIntegrand A Γ (hf i hi)),
    Finset.smul_sum]

theorem contourEval_pow_mul_const [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) (c : ℂ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n * c) = c • A ^ n := by
  simp_rw [mul_comm _ c]
  rw [contourEval_const_mul, contourEval_pow]

theorem contourEval_matrixPolynomial_entry [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) (i j : Fin m) :
    contourEval A Γ.toSmoothContour (fun z => matrixPolynomial B z i j) =
      ∑ k : Fin (d + 1), B k i j • A ^ (k : ℕ) := by
  have hc (k : Fin (d + 1)) : ContinuousOn (fun z : ℂ => z ^ (k : ℕ) * B k i j)
      Γ.toSmoothContour.trace := ((continuous_pow _).mul continuous_const).continuousOn
  simpa only [matrixPolynomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    contourEval_pow_mul_const] using
    contourEval_sum A Γ Finset.univ (fun k : Fin (d + 1) => fun z => z ^ (k : ℕ) * B k i j)
      (fun k _ => hc k)

theorem matrixContourEval_matrixPolynomial [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    matrixContourEval A Γ.toSmoothContour (matrixPolynomial B) = polynomialEval A B := by
  classical
  unfold matrixContourEval polynomialEval
  simp only [contourEval_matrixPolynomial_entry, ← tensorOperatorCLM_apply, map_sum]
  calc
    _ = ∑ i, ∑ k, ∑ j, tensorOperator (B k i j • A ^ (k : ℕ)) (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, tensorOperator (B k i j • A ^ (k : ℕ)) (Matrix.single i j 1) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact sum_tensorOperator_entries (A ^ (k : ℕ)) (B k)

theorem contourEval_polynomial [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (p : Polynomial ℂ) :
    contourEval A Γ.toSmoothContour p.eval = Polynomial.aeval A p := by
  simp_rw [Polynomial.eval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  rw [contourEval_sum A Γ (Finset.range (p.natDegree + 1))
    (fun k z => p.coeff k * z ^ k)
    (fun k _ => (continuous_const.mul (continuous_pow k)).continuousOn)]
  apply Finset.sum_congr rfl
  intro k _
  rw [contourEval_const_mul, contourEval_pow]

theorem contour_bound_of_uniform_polynomials [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ}
    (F : ℂ → Coeff m) (hF : ContinuousOn F (numericalClosure A))
    (hpoly : ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
      ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B))
    (degrees : ℕ → ℕ) (B : (n : ℕ) → Fin (degrees n + 1) → Coeff m)
    (happrox : TendstoUniformlyOn (fun n => matrixPolynomial (B n)) F atTop
      (numericalClosure A ∪ Γ.toSmoothContour.trace)) :
    ‖matrixContourEval A Γ.toSmoothContour F‖ ≤ 2 * supNorm (numericalClosure A) F :=
  contour_bound_of_polynomial_approximation A Γ F hF hpoly
    (fun _ B => matrixContourEval_matrixPolynomial A Γ B) degrees B happrox

theorem contourEval_congr (A : Operator H) (Γ : SmoothContour) {f g : ℂ → ℂ}
    (hfg : EqOn f g Γ.trace) : contourEval A Γ f = contourEval A Γ g := by
  unfold contourEval
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hfg (show Γ.path t ∈ Γ.trace from
    mem_image_of_mem _ (by simpa using ht))]

theorem contourEval_mul_sub_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (a : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => (z - a) * f z) =
      (A - algebraMap ℂ (Operator H) a) * contourEval A Γ.toSmoothContour f := by
  have he : (fun z => (z - a) * f z) = (fun z => z * f z) - (fun z => a * f z) := by
    ext z
    exact sub_mul _ _ _
  rw [he, contourEval_sub A Γ (f := fun z => z * f z) (g := fun z => a * f z)
    (continuousOn_id.mul hf) (continuousOn_const.mul hf),
    contourEval_mul_id_of_integral_eq_zero A Γ hf hzero, contourEval_const_mul]
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem SmoothContour.integral_deriv_div_eq_zero (Γ : SmoothContour) {a : ℂ}
    (ha : Γ.index a = 0) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - a)) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact (mul_eq_zero.mp ha).resolve_left hc

theorem contourEval_inv_sub [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {a : ℂ} (ha : a ∉ U) :
    contourEval A Γ.toSmoothContour (fun z => (z - a)⁻¹) =
      Ring.inverse (A - algebraMap ℂ (Operator H) a) := by
  have hatrace (z : ℂ) (hz : z ∈ Γ.toSmoothContour.trace) : z - a ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hz
    intro he
    exact ha (sub_eq_zero.mp he ▸ (Γ.avoids t ht).1)
  have hf : ContinuousOn (fun z : ℂ => (z - a)⁻¹) Γ.toSmoothContour.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ hatrace
  have hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t - a)⁻¹) = 0 := by
    simpa only [div_eq_mul_inv] using
      Γ.toSmoothContour.integral_deriv_div_eq_zero (Γ.index_outside a ha)
  have he := contourEval_mul_sub_of_integral_eq_zero A Γ a hf hzero
  have hcongr : contourEval A Γ.toSmoothContour (fun z => (z - a) * (z - a)⁻¹) = 1 := by
    calc
      _ = contourEval A Γ.toSmoothContour (fun _ => 1) :=
        contourEval_congr A Γ.toSmoothContour (fun z hz => mul_inv_cancel₀ (hatrace z hz))
      _ = 1 := contourEval_one A Γ
  have haK : a ∉ numericalClosure A := by
    intro h
    exact one_ne_zero ((Γ.index_inside a h).symm.trans (Γ.index_outside a ha))
  have hu : IsUnit (A - algebraMap ℂ (Operator H) a) := by
    have hu0 : IsUnit (algebraMap ℂ (Operator H) a - A) := by
      change a ∈ resolventSet ℂ A
      by_contra h
      exact haK (spectrum_subset_numericalClosure A h)
    simpa only [neg_sub] using hu0.neg
  have h := (Ring.inverse_mul_eq_iff_eq_mul (A - algebraMap ℂ (Operator H) a)
    1 (contourEval A Γ.toSmoothContour (fun z => (z - a)⁻¹)) hu).mpr
      (hcongr.symm.trans he)
  simpa only [mul_one] using h.symm

end CrouzeixHilbert

end

end OAI
