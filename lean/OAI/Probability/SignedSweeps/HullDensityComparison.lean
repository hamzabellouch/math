import OAI.Probability.SignedSweeps.DensityComparison
import OAI.Probability.SignedSweeps.PairTwirlLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma isClosed_quadratic_upper (x : E) (c : ℝ) :
    IsClosed {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c} := by
  apply isClosed_le _ continuous_const
  fun_prop

omit [FiniteDimensional ℂ E] in
lemma convex_quadratic_upper [FiniteDimensional ℂ E] (x : E) (c : ℝ) :
    Convex ℝ {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c} := by
  intro T hT S hS a b ha hb hab
  change (inner ℂ x ((a • T + b • S) x)).re ≤ c
  simp only [add_apply, smul_apply,
    ← Complex.coe_smul, inner_add_right, inner_smul_right, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    a * (inner ℂ x (T x)).re + b * (inner ℂ x (S x)).re ≤ a * c + b * c :=
      add_le_add (mul_le_mul_of_nonneg_left hT ha) (mul_le_mul_of_nonneg_left hS hb)
    _ = c := by rw [← add_mul, hab, one_mul]

lemma quadratic_upper_closed_convex {I : Type*}
    (R : I → E →ₗ[ℂ] E) (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    (x : E) (c : ℝ) (h : ∀ i, (inner ℂ x (R i x)).re ≤ c) :
    (inner ℂ x (M x)).re ≤ c := by
  apply closedConvexHull_min (t := {T : E →L[ℂ] E | (inner ℂ x (T x)).re ≤ c})
    _ (convex_quadratic_upper x c) (isClosed_quadratic_upper x c) hM
  rintro _ ⟨i,rfl⟩
  exact h i

lemma projection_norm_sq_le_of_hull_domination {I : Type*}
    (H A : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (hHH : H * H = H)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hdom : ((a : ℂ) • M.toLinearMap - H).IsPositive)
    (hb : ∀ i, ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(H * A).toContinuousLinearMap‖ ^ 2 ≤ a * c := by
  apply norm_sq_le_of_pointwise_sq _ (mul_nonneg ha hc)
  intro x
  have hd : 0 ≤ (inner ℂ (A x)
      (((a : ℂ) • M.toLinearMap - H) (A x))).re := hdom.re_inner_nonneg_right (A x)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right,
    inner_smul_right, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, projection_quadratic H hH hHH] at hd
  have hq : (inner ℂ (A x) (M (A x))).re ≤ c * ‖x‖ ^ 2 := by
    apply quadratic_upper_closed_convex R M hM
    intro i
    rw [positiveRoot_quadratic (R i) (hR i)]
    calc
      _ ≤ ‖(positiveRoot (R i) (hR i) * A).toContinuousLinearMap‖ ^ 2 * ‖x‖ ^ 2 := by
        simpa only [LinearMap.coe_toContinuousLinearMap', Module.End.mul_apply, mul_pow] using
          pow_le_pow_left₀ (norm_nonneg _)
            ((positiveRoot (R i) (hR i) * A).toContinuousLinearMap.le_opNorm x) 2
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)
  calc
    _ ≤ a * (inner ℂ (A x) (M (A x))).re := by simpa only [Module.End.mul_apply, ContinuousLinearMap.coe_coe] using sub_nonneg.mp hd
    _ ≤ a * (c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left hq ha
    _ = _ := by ring

lemma right_projection_norm_sq_le_of_hull_domination {I : Type*}
    (K A : E →ₗ[ℂ] E) (hK : K.IsSymmetric) (hKK : K * K = K)
    (S : I → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (M : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (S i).toContinuousLinearMap)))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hdom : ((b : ℂ) • M.toLinearMap - K).IsPositive)
    (hs : ∀ i, ‖(A * positiveRoot (S i) (hS i)).toContinuousLinearMap‖ ^ 2 ≤ c) :
    ‖(A * K).toContinuousLinearMap‖ ^ 2 ≤ b * c := by
  have hadj : ∀ i, ‖(positiveRoot (S i) (hS i) * A.adjoint).toContinuousLinearMap‖ ^ 2 ≤ c := by
    intro i
    rw [← (positiveRoot_positive (S i) (hS i)).isSymmetric.adjoint_eq,
      ← linear_adjoint_mul, linear_adjoint_norm]
    exact hs i
  have hh := projection_norm_sq_le_of_hull_domination K A.adjoint hK hKK S hS M hM hb hc hdom hadj
  rw [← hK.adjoint_eq, ← linear_adjoint_mul, linear_adjoint_norm] at hh
  exact hh

theorem one_sided_hull_density_comparison {I J : Type*}
    (H K P : E →ₗ[ℂ] E)
    (hH : H.IsSymmetric) (hHH : H * H = H)
    (hK : K.IsSymmetric) (hKK : K * K = K)
    (hP : P.IsSymmetric) (hPP : P * P = P)
    (R : I → E →ₗ[ℂ] E) (hR : ∀ i, (R i).IsPositive)
    (S : J → E →ₗ[ℂ] E) (hS : ∀ j, (S j).IsPositive)
    (M N : E →L[ℂ] E)
    (hM : M ∈ closedConvexHull ℝ (Set.range (fun i => (R i).toContinuousLinearMap)))
    (hN : N ∈ closedConvexHull ℝ (Set.range (fun j => (S j).toContinuousLinearMap)))
    (T : I → E →ₗ[ℂ] E) (hT : ∀ i, (T i).IsPositive)
    (hsupport : ∀ i, R i * spectralSupport (T i) (hT i) = R i)
    (hTK : ∀ i, T i * K = K * T i) (hTP : ∀ i, T i * P = P * T i)
    {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hdomH : ((a : ℂ) • M.toLinearMap - H).IsPositive)
    (hdomK : ((b : ℂ) • N.toLinearMap - K).IsPositive)
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
      · exact right_projection_norm_sq_le_of_hull_domination K
          (positiveRoot (R i) (hR i) * supportInverseRoot (T i) (hT i))
          hK hKK S hS N hN hb hc hdomK (hcell i)
      · rw [root_projection_norm_sq (T i) P (hT i) hP hPP (hTP i)]
        exact hglobal i
      · positivity
      · positivity
    have hh := projection_norm_sq_le_of_hull_domination H (K * P) hH hHH
      R hR M hM ha (by positivity : 0 ≤ (b * c) * t) hdomH hr
    have he : a * ((b * c) * t) = a * b * t * c := by ring
    rw [he] at hh
    simpa only [mul_assoc] using hh

end SignedSweeps
end

end OAI
