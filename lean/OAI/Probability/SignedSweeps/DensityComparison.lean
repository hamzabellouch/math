import OAI.Probability.SignedSweeps.SpectralCommute

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma linear_adjoint_norm (A : E →ₗ[ℂ] E) :
    ‖A.adjoint.toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  rw [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map]

lemma linear_adjoint_mul (A B : E →ₗ[ℂ] E) :
    (A * B).adjoint = B.adjoint * A.adjoint := by
  simp only [← LinearMap.star_eq_adjoint, star_mul]

lemma linear_mul_norm_le (A B : E →ₗ[ℂ] E) :
    ‖(A * B).toContinuousLinearMap‖ ≤ ‖A.toContinuousLinearMap‖ * ‖B.toContinuousLinearMap‖ :=
  ContinuousLinearMap.opNorm_comp_le A.toContinuousLinearMap B.toContinuousLinearMap

lemma linear_mul_norm_sq_le (A B : E →ₗ[ℂ] E) :
    ‖(A * B).toContinuousLinearMap‖ ^ 2 ≤
      ‖A.toContinuousLinearMap‖ ^ 2 * ‖B.toContinuousLinearMap‖ ^ 2 := by
  simpa only [mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) (linear_mul_norm_le A B) 2

lemma norm_sq_le_of_pointwise_sq (A : E →ₗ[ℂ] E) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ c * ‖x‖ ^ 2) : ‖A.toContinuousLinearMap‖ ^ 2 ≤ c := by
  have hh : ‖A.toContinuousLinearMap‖ ≤ Real.sqrt c := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro x hx
    apply (Real.le_sqrt (norm_nonneg _) hc).mpr
    change ‖A x‖ ^ 2 ≤ c
    simpa only [hx, one_pow, mul_one] using hA x
  exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (Real.sq_sqrt hc)

omit [FiniteDimensional ℂ E] in
lemma projection_quadratic [FiniteDimensional ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetric)
    (hPP : P * P = P) (x : E) :
    (inner ℂ x (P x)).re = ‖P x‖ ^ 2 := by
  calc
    _ = (inner ℂ x (P (P x))).re := by
      rw [← Module.End.mul_apply, hPP]
    _ = _ := by
      rw [← hP]
      simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma projection_norm_sq_le_of_domination {I : Type*} [Fintype I]
    (H A : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (hHH : H * H = H)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hdom : ((a : ℂ) • (∑ i, (w i : ℂ) • R i) - H).IsPositive)
    (hb : ∀ i, ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(H * A).toContinuousLinearMap‖ ^ 2 ≤ a * c := by
  apply norm_sq_le_of_pointwise_sq _ (mul_nonneg ha hc)
  intro x
  have hd : 0 ≤ (inner ℂ (A x)
      (((a : ℂ) • (∑ i, (w i : ℂ) • R i) - H) (A x))).re :=
    hdom.re_inner_nonneg_right (A x)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    inner_sub_right, inner_smul_right, inner_sum, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum] at hd
  have hquad (i : I) := positiveRoot_quadratic (R i) (hR i) (A x)
  simp_rw [hquad] at hd
  rw [projection_quadratic H hH hHH] at hd
  have hi (i : I) : ‖positiveRoot (R i) (hR i) (A x)‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 * ‖x‖ ^ 2 := by
        simpa only [LinearMap.coe_toContinuousLinearMap', Module.End.mul_apply, mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
          ((positiveRoot (R i) (hR i) * A).toContinuousLinearMap.le_opNorm x) 2
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
  calc
    _ ≤ a * ∑ i, w i * ‖positiveRoot (R i) (hR i) (A x)‖ ^ 2 := by
      simpa only [Module.End.mul_apply] using sub_nonneg.mp hd
    _ ≤ a * ∑ i, w i * (c * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hi i) (hw i)) ha
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul, mul_assoc]

lemma right_projection_norm_sq_le_of_domination {I : Type*} [Fintype I]
    (K A : E →ₗ[ℂ] E) (hK : K.IsSymmetric) (hKK : K * K = K)
    (S : I → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdom : ((b : ℂ) • (∑ i, (w i : ℂ) • S i) - K).IsPositive)
    (hs : ∀ i, ‖(A * positiveRoot (S i) (hS i)).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(A * K).toContinuousLinearMap‖ ^ 2 ≤ b * c := by
  have hadj : ∀ i, ‖(positiveRoot (S i) (hS i) * A.adjoint).toContinuousLinearMap‖ ^ 2 ≤ c := by
    intro i
    rw [← (positiveRoot_positive (S i) (hS i)).isSymmetric.adjoint_eq,
      ← linear_adjoint_mul, linear_adjoint_norm]
    exact hs i
  have hh := projection_norm_sq_le_of_domination K A.adjoint hK hKK S hS w hw hsum hb hc hdom hadj
  rw [← hK.adjoint_eq, ← linear_adjoint_mul, linear_adjoint_norm] at hh
  exact hh

lemma root_projection_norm_sq (T P : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hP : P.IsSymmetric) (hPP : P * P = P) (hTP : T * P = P * T) :
    ‖(positiveRoot T hT * P).toContinuousLinearMap‖ ^ 2 =
      ‖(T * P).toContinuousLinearMap‖ := by
  rw [← positiveSquare_norm]
  congr 2
  rw [positiveSquare, linear_adjoint_mul, hP.adjoint_eq,
    (positiveRoot_positive T hT).isSymmetric.adjoint_eq]
  calc
    _ = P * (positiveRoot T hT * positiveRoot T hT) * P := by simp only [mul_assoc]
    _ = T * P := by rw [positiveRoot_square, ← hTP, mul_assoc, hPP]

lemma supported_inverse_insertion (R T K P : E →ₗ[ℂ] E)
    (hR : R.IsPositive) (hT : T.IsPositive)
    (hsupport : R * spectralSupport T hT = R)
    (hTK : T * K = K * T) :
    positiveRoot R hR * K * P =
      (positiveRoot R hR * supportInverseRoot T hT * K) * (positiveRoot T hT * P) := by
  have hsup := positiveRoot_right_support R (spectralSupport T hT) hR
    (spectralSupport_positive T hT).isSymmetric hsupport
  have hcomm := positiveRoot_commute T K hT hTK
  symm
  calc
    _ = positiveRoot R hR * (supportInverseRoot T hT *
        (K * positiveRoot T hT)) * P := by simp only [mul_assoc]
    _ = positiveRoot R hR * (supportInverseRoot T hT *
        positiveRoot T hT) * K * P := by rw [← hcomm]; simp only [mul_assoc]
    _ = _ := by rw [supportInverseRoot_mul_root, hsup]

theorem one_sided_density_comparison
    {I J : Type*} [Fintype I] [Fintype J]
    (H K P : E →ₗ[ℂ] E)
    (hH : H.IsSymmetric) (hHH : H * H = H)
    (hK : K.IsSymmetric) (hKK : K * K = K)
    (hP : P.IsSymmetric) (hPP : P * P = P)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (S : J → E →ₗ[ℂ] E) (hS : ∀ j, (S j).IsPositive)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsumw : ∑ i, w i = 1)
    (v : J → ℝ) (hv : ∀ j, 0 ≤ v j) (hsumv : ∑ j, v j = 1)
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsPositive)
    (hsupport : ∀ i, R i * spectralSupport (T i) (hT i) = R i)
    (hTK : ∀ i, T i * K = K * T i) (hTP : ∀ i, T i * P = P * T i)
    {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hdomH : ((a : ℂ) • (∑ i, (w i : ℂ) • R i) - H).IsPositive)
    (hdomK : ((b : ℂ) • (∑ j, (v j : ℂ) • S j) - K).IsPositive)
    (hglobal : ∀ i, ‖(T i * P).toContinuousLinearMap‖ ≤ t)
    (hcell : ∀ i j, ‖(positiveRoot (R i) (hR i) * supportInverseRoot (T i) (hT i) *
      positiveRoot (S j) (hS j)).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(H * K * P).toContinuousLinearMap‖ ^ 2 ≤ min 1 (a * b * t * c) := by
  apply le_min
  · apply norm_sq_le_of_pointwise_sq _ (by norm_num)
    intro x
    have hh : ‖(H * K * P) x‖ ≤ ‖x‖ := by
      simp only [Module.End.mul_apply]
      exact (symmetric_projection_contraction H hH hHH _).trans
        ((symmetric_projection_contraction K hK hKK _).trans (symmetric_projection_contraction P hP hPP _))
    simpa only [one_mul] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  · have hr (i : I) :
        ‖(positiveRoot (R i) (hR i) * (K * P)).toContinuousLinearMap‖ ^ 2 ≤ (b * c) * t := by
      rw [← mul_assoc, supported_inverse_insertion (R i) (T i) K P
        (hR i) (hT i) (hsupport i) (hTK i)]
      apply (linear_mul_norm_sq_le _ _).trans
      apply mul_le_mul
      · exact right_projection_norm_sq_le_of_domination K
          (positiveRoot (R i) (hR i) * supportInverseRoot (T i) (hT i))
          hK hKK S hS v hv hsumv hb hc hdomK (hcell i)
      · rw [root_projection_norm_sq (T i) P (hT i) hP hPP (hTP i)]
        exact hglobal i
      · positivity
      · positivity
    have hh := projection_norm_sq_le_of_domination H (K * P) hH hHH
      R hR w hw hsumw ha (by positivity : 0 ≤ (b * c) * t) hdomH hr
    have he : a * ((b * c) * t) = a * b * t * c := by ring
    rw [he] at hh
    simpa only [mul_assoc] using hh

end SignedSweeps
end

end OAI
