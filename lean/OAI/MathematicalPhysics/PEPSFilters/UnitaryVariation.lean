import Mathlib

namespace OAI

/-! Unitary first variations and trace stationarity. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma deriv_conjugation_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F B : E →L[ℂ] E) (hB : star B = -B) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B) * F *
      star (NormedSpace.exp (t • B))) (B * F - F * B) 0 := by
  have hU : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B)) B 0 := by
    simpa using hasDerivAt_exp_smul_const B (0 : ℝ)
  have hd := (hU.mul_const F).mul hU.star
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, star_one,
    mul_one, hB, mul_neg, ← sub_eq_add_neg] at hd
  convert hd using 1

lemma stationary_of_unitary_max_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (v : E) (R F : E →L[ℂ] E)
    (hmax : ∀ U : unitary (E →L[ℂ] E),
      ‖(R * ((U : E →L[ℂ] E) * F * star (U : E →L[ℂ] E))) v‖ ≤ ‖(R * F) v‖) :
    ∀ B : E →L[ℂ] E, star B = -B →
      (inner ℂ ((R * F) v) ((R * (B * F - F * B)) v)).re = 0 := by
  intro B hB
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  let M (t : ℝ) := R * (NormedSpace.exp (t • B) * F * star (NormedSpace.exp (t • B)))
  have hM : HasDerivAt M (R * (B * F - F * B)) 0 :=
    (deriv_conjugation_clm F B hB).const_mul R
  have hy := ((ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hM
  have hy' : HasDerivAt (fun t : ℝ => M t v) ((R * (B * F - F * B)) v) 0 := by
    convert hy using 1 <;> rfl
  have hn0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hy'.inner ℂ hy')
  have hn : HasDerivAt (fun t : ℝ => ‖M t v‖ ^ 2)
      (2 * (inner ℂ (M 0 v) ((R * (B * F - F * B)) v)).re) 0 := by
    convert hn0 using 1 <;> try rfl
    · funext t
      change ‖M t v‖ ^ 2 = (inner ℂ (M t v) (M t v)).re
      exact norm_sq_eq_re_inner (𝕜 := ℂ) (M t v)
    · change 2 * (inner ℂ (M 0 v) ((R * (B * F - F * B)) v)).re =
        (inner ℂ (M 0 v) ((R * (B * F - F * B)) v) +
         inner ℂ ((R * (B * F - F * B)) v) (M 0 v)).re
      rw [Complex.add_re]
      have hs := inner_re_symm (𝕜 := ℂ) ((R * (B * F - F * B)) v) (M 0 v)
      change (inner ℂ ((R * (B * F - F * B)) v) (M 0 v)).re =
        (inner ℂ (M 0 v) ((R * (B * F - F * B)) v)).re at hs
      rw [hs]
      ring
  have hU (t : ℝ) : NormedSpace.exp (t • B) ∈ unitary (E →L[ℂ] E) := by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp [hB]
  have h0 : M 0 = R * F := by simp [M]
  have hx : IsLocalMax (fun t : ℝ => ‖M t v‖ ^ 2) 0 := by
    apply IsMaxOn.isLocalMax (s := Set.univ) _ (by simp)
    intro t ht
    simp only [h0]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmax ⟨_, hU t⟩) 2
  have he := hx.hasDerivAt_eq_zero hn
  rw [h0] at he
  linarith

lemma stationary_of_unitary_max (v : EuclideanSpace ℂ n) (R F : Matrix n n ℂ)
    (hmax : ∀ U : unitary (Matrix n n ℂ),
      ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))
          (R * ((U : Matrix n n ℂ) * F * star (U : Matrix n n ℂ))) v‖ ≤
        ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (R * F) v‖) :
    ∀ B : Matrix n n ℂ, star B = -B →
      (inner ℂ ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (R * F) v)
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) (R * (B * F - F * B)) v)).re = 0 := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hm : ∀ U : unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
      ‖(e R * ((U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) * e F *
        star (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))) v‖ ≤ ‖(e R * e F) v‖ := by
    intro U
    have hu : e.symm (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) ∈ unitary _ := by
      constructor
      · apply e.injective
        change e (star (e.symm ↑U) * e.symm ↑U) = e 1
        rw [map_mul, map_star, e.apply_symm_apply, map_one]
        exact U.property.1
      · apply e.injective
        change e (e.symm ↑U * star (e.symm ↑U)) = e 1
        rw [map_mul, map_star, e.apply_symm_apply, map_one]
        exact U.property.2
    have ht := hmax ⟨_, hu⟩
    change ‖e (R * (e.symm ↑U * F * star (e.symm ↑U))) v‖ ≤ ‖e (R * F) v‖ at ht
    simpa only [map_mul, map_star, e.apply_symm_apply] using ht
  intro B hB
  have hb : star (e B) = -(e B) := by rw [← map_star, hB, map_neg]
  have hs := stationary_of_unitary_max_clm v (e R) (e F) hm (e B) hb
  simpa only [map_mul, map_sub] using hs

lemma deriv_conjugation_matrix (F B : Matrix n n ℂ) (hB : star B = -B) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B) * F *
      star (NormedSpace.exp (t • B))) (B * F - F * B) 0 := by
  have hU : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • B)) B 0 := by
    simpa using hasDerivAt_exp_smul_const B (0 : ℝ)
  have hd := (hU.mul_const F).mul hU.star
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, star_one,
    mul_one, hB, mul_neg, ← sub_eq_add_neg] at hd
  convert hd using 1

lemma re_inner_deriv_eq_zero_of_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {y : ℝ → E} {d : E}
    (hy : HasDerivAt y d 0) (hmax : ∀ t, ‖y t‖ ≤ ‖y 0‖) :
    (inner ℂ (y 0) d).re = 0 := by
  have hn0 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hy.inner ℂ hy)
  have hn : HasDerivAt (fun t : ℝ => ‖y t‖ ^ 2)
      (2 * (inner ℂ (y 0) d).re) 0 := by
    convert hn0 using 1 <;> try rfl
    · funext t
      change ‖y t‖ ^ 2 = (inner ℂ (y t) (y t)).re
      exact norm_sq_eq_re_inner (𝕜 := ℂ) (y t)
    · change 2 * (inner ℂ (y 0) d).re =
        (inner ℂ (y 0) d + inner ℂ d (y 0)).re
      rw [Complex.add_re]
      have hs := inner_re_symm (𝕜 := ℂ) d (y 0)
      change (inner ℂ d (y 0)).re = (inner ℂ (y 0) d).re at hs
      rw [hs]
      ring
  have hx : IsLocalMax (fun t : ℝ => ‖y t‖ ^ 2) 0 := by
    apply IsMaxOn.isLocalMax (s := Set.univ) _ (by simp)
    intro t _
    exact pow_le_pow_left₀ (norm_nonneg _) (hmax t) 2
  have he := hx.hasDerivAt_eq_zero hn
  linarith

end PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma hermitian_of_skew_trace (A : Matrix n n ℂ)
    (h : ∀ B : Matrix n n ℂ, star B = -B → (A * B).trace.re = 0) :
    A.IsHermitian := by
  have hB : star (star A - A) = -(star A - A) := by
    simp only [star_sub, star_star]
    abel
  have hz := h (star A - A) hB
  have he : ((A - star A).conjTranspose * (A - star A)).trace =
      (A * (star A - A)).trace + star (A * (star A - A)).trace := by
    rw [← Matrix.trace_conjTranspose (A * (star A - A))]
    simp only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm A.conjTranspose A]
    abel
  have ht : ((A - star A).conjTranspose * (A - star A)).trace = 0 := by
    rw [he]
    apply Complex.ext <;> simp [hz]
  have hd : A - star A = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht
  exact (sub_eq_zero.mp hd).symm

omit [DecidableEq n] in
lemma trace_re_hermitian_skew {ρ B : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hB : star B = -B) : (ρ * B).trace.re = 0 := by
  have hs : star (ρ * B).trace = -(ρ * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
    change (star B * star ρ).trace = _
    rw [hB, show star ρ = ρ from hρ, Matrix.neg_mul, Matrix.trace_neg,
      Matrix.trace_mul_comm B ρ]
  have he := congrArg Complex.re hs
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at he
  linarith

lemma commute_of_unitary_trace_stationarity {ρ F : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hF : F.PosSemidef) (hdet : IsUnit F.det)
    (h : ∀ B : Matrix n n ℂ, star B = -B →
      (ρ * (B - F * B * F⁻¹)).trace.re = 0) : Commute F ρ := by
  have hi : F⁻¹.conjTranspose = F⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hF.isHermitian]
  have hh : (F⁻¹ * ρ * F).IsHermitian := by
    apply hermitian_of_skew_trace
    intro B hB
    have hz := h B hB
    have he : (ρ * (F * B * F⁻¹)).trace = ((F⁻¹ * ρ * F) * B).trace := by
      rw [← Matrix.mul_assoc ρ, Matrix.trace_mul_comm (ρ * (F * B)) F⁻¹]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, he,
      trace_re_hermitian_skew hρ hB] at hz
    linarith
  have hs : F * ρ * F⁻¹ = F⁻¹ * ρ * F := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_mul, show F.conjTranspose = F from hF.isHermitian,
      show ρ.conjTranspose = ρ from hρ, hi, Matrix.mul_assoc] using hh
  have he := congrArg (fun M : Matrix n n ℂ => F * M * F) hs
  have he' : F * F * ρ = ρ * (F * F) := by
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul F hdet, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left F _ hdet] using he
  have hc : Commute (F * F) ρ := he'
  have hr := hc.cfcₙ_nnreal NNReal.sqrt
  change Commute (CFC.sqrt (F * F)) ρ at hr
  simpa only [CFC.sqrt_mul_self F hF.nonneg] using hr

end PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity

end

end OAI
