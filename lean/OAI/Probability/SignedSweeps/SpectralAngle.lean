import OAI.Probability.SignedSweeps.MomentMonotonicity
import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma trace_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    (LinearMap.trace ℂ E T).re = ∑ i : Fin (Module.finrank ℂ E), hT.eigenvalues rfl i := by
  simpa only [pow_one] using trace_power_spectral T hT 1

lemma quadratic_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
    (inner ℂ x (T x)).re = ∑ i : Fin (Module.finrank ℂ E),
      hT.eigenvalues rfl i * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner x (T x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hT (hT.eigenvectorBasis rfl i) x, hT.apply_eigenvectorBasis,
    inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  rw [show inner ℂ x (hT.eigenvectorBasis rfl i) *
      ((hT.eigenvalues rfl i : ℂ) * inner ℂ (hT.eigenvectorBasis rfl i) x) =
      (hT.eigenvalues rfl i : ℂ) * (inner ℂ (hT.eigenvectorBasis rfl i) x *
        inner ℂ x (hT.eigenvectorBasis rfl i)) by ring,
    ← inner_conj_symm x (hT.eigenvectorBasis rfl i), Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq]

lemma eigenvector_mem_range (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ E)) (hi : hT.eigenvalues rfl i ≠ 0) :
    hT.eigenvectorBasis rfl i ∈ T.range := by
  apply LinearMap.mem_range.mpr
  refine ⟨((hT.eigenvalues rfl i : ℂ)⁻¹) • hT.eigenvectorBasis rfl i, ?_⟩
  rw [map_smul, hT.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast hi

lemma trace_product_spectral (X Y : E →ₗ[ℂ] E) (hX : X.IsSymmetric) :
    (LinearMap.trace ℂ E (X * Y)).re =
      ∑ i : Fin (Module.finrank ℂ E), hX.eigenvalues rfl i *
        (inner ℂ (hX.eigenvectorBasis rfl i) (Y (hX.eigenvectorBasis rfl i))).re := by
  rw [LinearMap.trace_eq_sum_inner _ (hX.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, ← hX, hX.apply_eigenvectorBasis, inner_smul_left,
    RCLike.conj_ofReal, RCLike.ofReal_eq_complex_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma positive_trace_product_nonneg (X Y : E →ₗ[ℂ] E)
    (hX : X.IsPositive) (hY : Y.IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (X * Y)).re := by
  rw [trace_product_spectral X Y hX.isSymmetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hX.nonneg_eigenvalues rfl i)
    ((Complex.nonneg_iff.mp (hY.inner_nonneg_right _)).1)

lemma positive_trace_product_le_squared_angle (X Y : E →ₗ[ℂ] E)
    (hX : X.IsPositive) (hY : Y.IsPositive) (a : ℝ)
    (hangle : ∀ x ∈ X.range, ∀ y ∈ Y.range,
      ‖inner ℂ x y‖ ^ 2 ≤ a * ‖x‖ ^ 2 * ‖y‖ ^ 2) :
    (LinearMap.trace ℂ E (X * Y)).re ≤
      a * (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  classical
  rw [trace_product_spectral X Y hX.isSymmetric,
    trace_spectral X hX.isSymmetric, trace_spectral Y hY.isSymmetric]
  simp_rw [quadratic_spectral Y hY.isSymmetric, Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℂ E), ∑ j : Fin (Module.finrank ℂ E),
        hX.isSymmetric.eigenvalues rfl i * (hY.isSymmetric.eigenvalues rfl j * a) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hi : hX.isSymmetric.eigenvalues rfl i = 0
      · simp [hi]
      by_cases hj : hY.isSymmetric.eigenvalues rfl j = 0
      · simp [hj]
      apply mul_le_mul_of_nonneg_left _ (hX.nonneg_eigenvalues rfl i)
      apply mul_le_mul_of_nonneg_left _ (hY.nonneg_eigenvalues rfl j)
      have hh := hangle _ (eigenvector_mem_range X hX.isSymmetric i hi)
        _ (eigenvector_mem_range Y hY.isSymmetric j hj)
      simpa only [OrthonormalBasis.norm_eq_one, one_pow, mul_one, norm_inner_symm] using hh
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma fixed_squared_inner_le_composition (A B C : E →ₗ[ℂ] E) (hA : A.IsSymmetric)
    {x y : E} (hAx : A x = x) (hBy : B y = y) (hCy : C y = y) :
    ‖inner ℂ x y‖ ^ 2 ≤ ‖(A * B * C).toContinuousLinearMap‖ ^ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have he : inner ℂ x y = inner ℂ x ((A * B * C) y) := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hCy, hBy, ← hA x y, hAx]
  have hb : ‖inner ℂ x y‖ ≤ ‖x‖ * (‖(A * B * C).toContinuousLinearMap‖ * ‖y‖) := by
    rw [he]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left ((A * B * C).toContinuousLinearMap.le_opNorm y) (norm_nonneg x))
  calc
    _ ≤ (‖x‖ * (‖(A * B * C).toContinuousLinearMap‖ * ‖y‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by ring

lemma positive_trace_product_le_three_projection_norm
    (X Y A B C : E →ₗ[ℂ] E) (hX : X.IsPositive) (hY : Y.IsPositive)
    (hA : A.IsSymmetric) (hAX : A * X = X) (hBY : B * Y = Y) (hCY : C * Y = Y) :
    (LinearMap.trace ℂ E (X * Y)).re ≤
      ‖(A * B * C).toContinuousLinearMap‖ ^ 2 *
        (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  apply positive_trace_product_le_squared_angle X Y hX hY
  intro x hx y hy
  obtain ⟨x₀, rfl⟩ := LinearMap.mem_range.mp hx
  obtain ⟨y₀, rfl⟩ := LinearMap.mem_range.mp hy
  apply fixed_squared_inner_le_composition A B C hA
  · exact LinearMap.congr_fun hAX x₀
  · exact LinearMap.congr_fun hBY y₀
  · exact LinearMap.congr_fun hCY y₀

omit [FiniteDimensional ℂ E] in
lemma symmetric_projection_contraction [FiniteDimensional ℂ E]
    (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) : ‖P x‖ ≤ ‖x‖ := by
  have hh : ‖P x‖ ^ 2 = (inner ℂ x (P x)).re := by
    calc
      _ = (inner ℂ (P x) (P x)).re := by
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
          ← Complex.ofReal_pow, Complex.ofReal_re]
      _ = _ := by rw [hP, ← Module.End.mul_apply, hPP]
  have hb : (inner ℂ x (P x)).re ≤ ‖x‖ * ‖P x‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg x, norm_nonneg (P x)]

lemma positive_projection_trace_le (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) :
    (LinearMap.trace ℂ E (X * P)).re ≤ (LinearMap.trace ℂ E X).re := by
  rw [trace_product_spectral X P hX.isSymmetric, trace_spectral X hX.isSymmetric]
  apply Finset.sum_le_sum
  intro i _
  have hb : (inner ℂ (hX.isSymmetric.eigenvectorBasis rfl i)
      (P (hX.isSymmetric.eigenvectorBasis rfl i))).re ≤ 1 := by
    calc
      _ ≤ ‖hX.isSymmetric.eigenvectorBasis rfl i‖ *
          ‖P (hX.isSymmetric.eigenvectorBasis rfl i)‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ ‖hX.isSymmetric.eigenvectorBasis rfl i‖ *
          ‖hX.isSymmetric.eigenvectorBasis rfl i‖ :=
        mul_le_mul_of_nonneg_left (symmetric_projection_contraction P hP hPP _) (norm_nonneg _)
      _ = 1 := by simp only [OrthonormalBasis.norm_eq_one, one_mul]
  exact (mul_le_mul_of_nonneg_left hb (hX.nonneg_eigenvalues rfl i)).trans_eq (mul_one _)

lemma positive_commuting_projection (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) (hPX : P * X = X * P) :
    (P * X).IsPositive := by
  have he : P * X * P = P * X := by
    rw [mul_assoc, ← hPX, ← mul_assoc, hPP]
  have hp := hX.conj_adjoint P
  rw [hP.adjoint_eq] at hp
  change (P * X * P).IsPositive at hp
  exact he ▸ hp

lemma positive_global_projection_trace_bound
    (X Y A B P : E →ₗ[ℂ] E) (hX : X.IsPositive) (hY : Y.IsPositive)
    (hA : A.IsSymmetric) (hP : P.IsSymmetric) (hPP : P * P = P)
    (hPX : P * X = X * P) (hPY : P * Y = Y * P)
    (hAX : A * X = X) (hBY : B * Y = Y) :
    (LinearMap.trace ℂ E (P * X * Y)).re ≤
      ‖(A * B * P).toContinuousLinearMap‖ ^ 2 *
        (LinearMap.trace ℂ E X).re * (LinearMap.trace ℂ E Y).re := by
  have hPXpos := positive_commuting_projection X P hX hP hPP hPX
  have hPYpos := positive_commuting_projection Y P hY hP hPP hPY
  have hprod : (P * X) * (P * Y) = P * X * Y := by
    rw [← mul_assoc, mul_assoc P X P, ← hPX, ← mul_assoc P P X, hPP]
  have hAfix : A * (P * X) = P * X := by
    rw [hPX, ← mul_assoc, hAX]
  have hBfix : B * (P * Y) = P * Y := by
    rw [hPY, ← mul_assoc, hBY]
  have hPfix : P * (P * Y) = P * Y := by rw [← mul_assoc, hPP]
  have hb := positive_trace_product_le_three_projection_norm (P * X) (P * Y)
    A B P hPXpos hPYpos hA hAfix hBfix hPfix
  rw [hprod] at hb
  have htx : (LinearMap.trace ℂ E (P * X)).re ≤ (LinearMap.trace ℂ E X).re := by
    rw [hPX]
    exact positive_projection_trace_le X P hX hP hPP
  have hty : (LinearMap.trace ℂ E (P * Y)).re ≤ (LinearMap.trace ℂ E Y).re := by
    rw [hPY]
    exact positive_projection_trace_le Y P hY hP hPP
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left htx (sq_nonneg _)) hty
    (Complex.re_le_re hPYpos.trace_nonneg) (mul_nonneg (sq_nonneg _) (Complex.re_le_re hX.trace_nonneg))

end SignedSweeps
end

end OAI
