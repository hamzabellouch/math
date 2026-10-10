import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Clipping
import OAI.MathematicalPhysics.PEPSFilters.Bipartite
import OAI.MathematicalPhysics.PEPSFilters.SchmidtPairing

namespace OAI

/-! Operator expectation expansions and regularized single-crossing energy bounds. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
open scoped BigOperators InnerProductSpace

open scoped BigOperators
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_sum_real_smul (v : ι → E) (c d : ι → ℝ) (H : E →L[ℂ] E) :
    inner ℂ (∑ i, (c i : ℂ) • v i) (H (∑ k, (d k : ℂ) • v k)) =
      ∑ i, ∑ k, ((c i * d k : ℝ) : ℂ) * inner ℂ (v i) (H (v k)) := by
  rw [sum_inner]
  simp only [inner_smul_left, map_sum, map_smul, inner_sum, inner_smul_right,
    Complex.conj_ofReal, Complex.ofReal_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  ring

lemma eigenvector_sum (v : ι → E) (c l : ι → ℝ) (T : E →L[ℂ] E)
    (hT : ∀ i, T (v i) = (l i : ℂ) • v i) :
    T (∑ i, (c i : ℂ) • v i) = ∑ i, ((c i*l i : ℝ) : ℂ) • v i := by
  simp only [map_sum, map_smul, hT, smul_smul, Complex.ofReal_mul]

lemma similarity_expectation_expansion (T S H : E →L[ℂ] E)
    (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (v : ι → E) (p l : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (heT : ∀ i, T (v i) = (l i : ℂ) • v i)
    (heS : ∀ i, S (v i) = ((l i)⁻¹ : ℝ) • v i) :
    let ψ := ∑ i, (Real.sqrt (p i) : ℂ) • v i
    (inner ℂ ψ (T (H (S ψ)))).re - (inner ℂ ψ (H ψ)).re =
      ∑ i, ∑ k, Real.sqrt (p i*p k) * (l i/l k-1) * (inner ℂ (v i) (H (v k))).re := by
  let ψ := ∑ i, (Real.sqrt (p i) : ℂ) • v i
  have hS : ∀ i, S (v i) = (((l i)⁻¹ : ℝ) : ℂ) • v i := by
    intro i
    simpa only [Complex.coe_smul] using heS i
  change (inner ℂ ψ (T (H (S ψ)))).re - (inner ℂ ψ (H ψ)).re = _
  rw [← hT]
  change (inner ℂ (T (∑ i, (Real.sqrt (p i) : ℂ) • v i))
      (H (S (∑ i, (Real.sqrt (p i) : ℂ) • v i)))).re -
      (inner ℂ (∑ i, (Real.sqrt (p i) : ℂ) • v i)
        (H (∑ i, (Real.sqrt (p i) : ℂ) • v i))).re = _
  rw [eigenvector_sum v (fun i => Real.sqrt (p i)) l T heT,
    eigenvector_sum v (fun i => Real.sqrt (p i)) (fun i => (l i)⁻¹) S hS,
    inner_sum_real_smul, inner_sum_real_smul]
  simp only [Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  rw [Real.sqrt_mul (hp i)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

omit [Fintype ι] in
lemma hermitian_coefficients (H : E →L[ℂ] E)
    (hH : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) (v : ι → E) :
    ∀ i k, inner ℂ (v i) (H (v k)) = star (inner ℂ (v k) (H (v i))) := by
  intro i k
  rw [← hH, ← inner_conj_symm]
  rfl
end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

lemma tensorState_smul_left (A : Finset (Vertex L))
    (e : EuclideanSpace ℂ (RegionConfiguration q A))
    (f : EuclideanSpace ℂ (RegionConfiguration q Aᶜ)) (c : ℂ) :
    tensorState A (c • e) f = c • tensorState A e f := by
  ext x
  simp only [tensorState, PiLp.smul_apply, WithLp.ofLp_toLp, smul_eq_mul, mul_assoc]

lemma physical_one_crossing {ν : Type*} [Fintype ν]
    (A : Finset (Vertex L)) (ψ : State L q) (hψ : ‖ψ‖ = 1)
    (U : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ))
    (r : RegionConfiguration q A → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hρ : reducedDensity ψ A = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (r i : ℂ))))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (l : RegionConfiguration q A → ℝ) (hl : ∀ i, 0 < l i)
    (hlog : ∀ i k, 0 < r i → 0 < r k →
      |Real.log (l i) - Real.log (l k)| ≤ a/2 * |Real.log (r i) - Real.log (r k)|)
    (B : ν → Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (C : ν → Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (H : Operator L q) (hH : H.IsHermitian)
    (hprod : H = ∑ z, liftLocal A (B z) * liftLocal Aᶜ (C z)) :
    let T := asMap (liftLocal A (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (l i : ℂ)))))
    let S := asMap (liftLocal A (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => ((l i)⁻¹ : ℂ)))))
    |(inner ℂ ψ (T (asMap H (S ψ)))).re - (inner ℂ ψ (asMap H ψ)).re| ≤
      a^2 * ∑ z, ‖B z‖ * ‖C z‖ := by
  classical
  let D := star (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) * coefficientMatrix ψ A
  let e : schmidtIndex r → EuclideanSpace ℂ (RegionConfiguration q A) :=
    fun i => columnVector (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ) i
  let f := schmidtRight D r
  let v : schmidtIndex r → State L q := fun i => tensorState A (e i) (f i)
  let T := asMap (liftLocal A (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (l i : ℂ)))))
  let S := asMap (liftLocal A (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => ((l i)⁻¹ : ℂ)))))
  have he : Orthonormal ℂ e := (orthonormal_columns U).comp Subtype.val Subtype.val_injective
  have hf : Orthonormal ℂ f := orthonormal_schmidtRight D r
    (rotated_density_diagonal (coefficientMatrix ψ A) U r hρ)
  have hdecomp : ψ = ∑ i : schmidtIndex r, (Real.sqrt (r i) : ℂ) • v i :=
    physical_schmidt_decomposition A ψ U r hr hρ
  have hs : ∑ i : schmidtIndex r, r i = 1 := sum_schmidt_probabilities A ψ hψ U r hr hρ
  have ht : ∀ i : schmidtIndex r, T (v i) = (l i : ℂ) • v i := by
    intro i
    dsimp only [T, v, e]
    rw [asMap_liftLocal_tensorState, diagonal_conjugate_column, tensorState_smul_left]
  have hsinv : ∀ i : schmidtIndex r, S (v i) = ((l i)⁻¹ : ℝ) • v i := by
    intro i
    dsimp only [S, v, e]
    rw [asMap_liftLocal_tensorState]
    have hh := diagonal_conjugate_column U (fun k => (l k)⁻¹) i.val
    have hh' := congrArg (fun u => tensorState A u (f i)) hh
    rw [tensorState_smul_left] at hh'
    simpa only [← Complex.ofReal_inv, Complex.coe_smul] using hh'
  have hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y) := by
    have hd : (Matrix.diagonal (fun i => (l i : ℂ))).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast (hl i).le)
    exact asMap_inner_hermitian (liftLocal_positive A
      (hd.mul_mul_conjTranspose_same (U : Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ))).isHermitian
  have hexp : ∀ i k : schmidtIndex r, inner ℂ (v i) (asMap H (v k)) =
      ∑ z, inner ℂ (e i) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (B z)) (e k)) *
        inner ℂ (f i) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (C z)) (f k)) := by
    intro i k
    rw [hprod, asMap_sum, inner_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [asMap_mul]
    dsimp only [v]
    rw [asMap_liftComplement_tensorState, asMap_liftLocal_tensorState, inner_tensorState]
  have hb := one_crossing_schmidt_bound a ha ha1 (fun i : schmidtIndex r => r i)
    (fun i => hr i) hs (fun i => l i) (fun i => hl i)
    (fun i k _ _ => hlog i k i.property k.property)
    (fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (B z))
    (fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (C z)) e f he hf
    (fun i k => inner ℂ (v i) (asMap H (v k)))
    (hermitian_coefficients (asMap H) (asMap_inner_hermitian hH) v) hexp
  have hex := similarity_expectation_expansion T S (asMap H) hT v
    (fun i : schmidtIndex r => r i) (fun i => l i) (fun i => hr i) ht hsinv
  change |(inner ℂ ψ (T (asMap H (S ψ)))).re - (inner ℂ ψ (asMap H ψ)).re| ≤ _
  rw [← hdecomp] at hex
  rw [hex]
  simpa only [StarAlgEquiv.norm_map] using hb

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
open Matrix
variable {L q : ℕ}

lemma reducedDensity_real_smul (A : Finset (Vertex L)) (ψ : State L q) (c : ℝ) :
    reducedDensity ((c : ℂ) • ψ) A = ((c^2 : ℝ) : ℂ) • reducedDensity ψ A := by
  have hC : coefficientMatrix ((c : ℂ) • ψ) A = (c : ℂ) • coefficientMatrix ψ A := by
    ext x y
    simp only [coefficientMatrix, PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [reducedDensity, hC, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [RCLike.star_def, Complex.conj_ofReal, pow_two]
  simp only [Complex.ofReal_mul, reducedDensity]

lemma normalized_density_diagonal (A : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ))
    (r : RegionConfiguration q A → ℝ)
    (hρ : reducedDensity ψ A = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (r i : ℂ)))) (c : ℝ) :
    reducedDensity ((c : ℂ) • ψ) A = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (c^2 * r i : ℂ))) := by
  rw [reducedDensity_real_smul, hρ, ← map_smul]
  congr 1
  ext i k
  by_cases h : i = k
  · subst k; simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul, Complex.ofReal_pow]
  · simp [h]

lemma norm_normalized (ψ : State L q) (hψ : ψ ≠ 0) : ‖((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hψ))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ)

lemma clipped_power_log_ratio {n : Type*} (x r : n → ℝ) {b c a : ℝ}
    (hb : 0 < b) (hc : 0 < c) (ha : 0 ≤ a)
    (hx : ∀ i, 0 ≤ x i)
    (hclip : ∀ i, x i + b = max b (r i / c)) (i k : n)
    (hir : 0 < r i) (hkr : 0 < r k) :
    |Real.log ((x i+b)^(a/2)) - Real.log ((x k+b)^(a/2))| ≤
      a/2 * |Real.log (r i) - Real.log (r k)| := by
  rw [Real.log_rpow (by linarith [hx i] : 0 < x i+b), Real.log_rpow (by linarith [hx k] : 0 < x k+b)]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a/2), hclip i, hclip k]
  exact mul_le_mul_of_nonneg_left (clipped_log_lipschitz hb hc hir hkr) (by positivity)

lemma log_scaled_difference {c x y : ℝ} (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    Real.log (c*x) - Real.log (c*y) = Real.log x - Real.log y := by
  rw [Real.log_mul hc.ne' hx.ne', Real.log_mul hc.ne' hy.ne']
  ring

lemma inverse_conjugate_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (l : n → ℝ) (hl : ∀ i, l i ≠ 0) :
    (Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => (l i : ℂ))))⁻¹ =
      Unitary.conjStarAlgAut ℂ _ U (Matrix.diagonal (fun i => ((l i)⁻¹ : ℂ))) := by
  apply Matrix.inv_eq_right_inv
  rw [← map_mul]
  have hd : Matrix.diagonal (fun i => (l i : ℂ)) * Matrix.diagonal (fun i => ((l i)⁻¹ : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hl _)), Matrix.diagonal_one]
  rw [hd, map_one]

lemma regularized_one_crossing {ν : Type*} [Fintype ν]
    (A : Finset (Vertex L)) (φ : State L q) (hφ : φ ≠ 0)
    (p : SpectralCoordinate (RegionConfiguration q A))
    (r : RegionConfiguration q A → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hρ : reducedDensity φ A = Unitary.conjStarAlgAut ℂ _ p.1
      (Matrix.diagonal (fun i => (r i : ℂ))))
    {b c a : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hclip : ∀ i, p.2.val i+b = max b (r i/c))
    (B : ν → Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)
    (C : ν → Matrix (RegionConfiguration q Aᶜ) (RegionConfiguration q Aᶜ) ℂ)
    (H : Operator L q) (hH : H.IsHermitian)
    (hprod : H = ∑ z, liftLocal A (B z) * liftLocal Aᶜ (C z)) :
    let ψ := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ
    let F := regularizedCoordinateMatrix b a p
    |(inner ℂ ψ (asMap (liftLocal A F) (asMap H (asMap (liftLocal A F⁻¹) ψ)))).re -
      (inner ℂ ψ (asMap H ψ)).re| ≤ a^2 * ∑ z, ‖B z‖ * ‖C z‖ := by
  classical
  let d : ℝ := ‖φ‖⁻¹
  let ψ := (d : ℂ) • φ
  let r' := fun i => d^2 * r i
  let l := fun i => (p.2.val i+b)^(a/2)
  have hd : 0 < d := inv_pos.mpr (norm_pos_iff.mpr hφ)
  have hl (i) : 0 < l i := Real.rpow_pos_of_pos (by linarith [(p.2.property).1 i]) _
  have hr' (i) : 0 ≤ r' i := mul_nonneg (sq_nonneg d) (hr i)
  have hlog : ∀ i k, 0 < r' i → 0 < r' k →
      |Real.log (l i) - Real.log (l k)| ≤ a/2 * |Real.log (r' i) - Real.log (r' k)| := by
    intro i k hi hk
    have hir : 0 < r i := (mul_pos_iff_of_pos_left (sq_pos_of_pos hd)).mp hi
    have hkr : 0 < r k := (mul_pos_iff_of_pos_left (sq_pos_of_pos hd)).mp hk
    dsimp only [r']
    rw [log_scaled_difference (sq_pos_of_pos hd) hir hkr]
    exact clipped_power_log_ratio p.2.val r hb hc ha p.2.property.1 hclip i k hir hkr
  have hρ' : reducedDensity ψ A = Unitary.conjStarAlgAut ℂ _ p.1
      (Matrix.diagonal (fun i => (r' i : ℂ))) := by
    simpa only [r', Complex.ofReal_mul, Complex.ofReal_pow] using
      normalized_density_diagonal A φ p.1 r hρ d
  have he := physical_one_crossing A ψ (norm_normalized φ hφ) p.1 r' hr'
    hρ' a ha ha1 l hl hlog B C H hH hprod
  have hi := inverse_conjugate_diagonal p.1 l (fun i => (hl i).ne')
  dsimp only [regularizedCoordinateMatrix]
  rw [hi]
  exact he

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

end

end OAI
