import OAI.Probability.SignedSweeps.ProvedRanges3

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def basisDiagonal {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) : E →ₗ[ℂ] E :=
  b.toBasis.constr ℂ (fun i => (c i : ℂ) • b i)

omit [FiniteDimensional ℂ E] in
@[simp] lemma basisDiagonal_apply_basis [FiniteDimensional ℂ E] {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (i : I) :
    basisDiagonal b c (b i) = (c i : ℂ) • b i :=
  b.toBasis.constr_basis ℂ _ i

lemma basisDiagonal_toMatrix {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) :
    LinearMap.toMatrix b.toBasis b.toBasis (basisDiagonal b c) =
      Matrix.diagonal (fun i => (c i : ℂ)) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    basisDiagonal_apply_basis, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  split_ifs with h <;> simp_all

lemma basisDiagonal_positive {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (basisDiagonal b c).IsPositive := by
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  rw [basisDiagonal_toMatrix, Matrix.posSemidef_diagonal_iff]
  intro i
  exact Complex.nonneg_iff.mpr ⟨hc i, rfl⟩

lemma basisDiagonal_mul {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c d : I → ℝ) :
    basisDiagonal b c * basisDiagonal b d = basisDiagonal b (fun i => c i * d i) := by
  apply b.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, Module.End.mul_apply, basisDiagonal_apply_basis,
    map_smul, smul_smul, Complex.ofReal_mul]
  rw [mul_comm]

def positiveRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => Real.sqrt (hT.isSymmetric.eigenvalues rfl i))

def supportInverseRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => (Real.sqrt (hT.isSymmetric.eigenvalues rfl i))⁻¹)

def spectralSupport (T : E →ₗ[ℂ] E) (hT : T.IsPositive) : E →ₗ[ℂ] E :=
  basisDiagonal (hT.isSymmetric.eigenvectorBasis rfl)
    (fun i => if hT.isSymmetric.eigenvalues rfl i = 0 then 0 else 1)

lemma positiveRoot_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (positiveRoot T hT).IsPositive :=
  basisDiagonal_positive _ _ (fun _ => Real.sqrt_nonneg _)

lemma supportInverseRoot_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (supportInverseRoot T hT).IsPositive :=
  basisDiagonal_positive _ _ (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

lemma spectralSupport_positive (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    (spectralSupport T hT).IsPositive := by
  apply basisDiagonal_positive
  intro i
  split_ifs <;> norm_num

lemma positiveRoot_square (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * positiveRoot T hT = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [positiveRoot, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    basisDiagonal_apply_basis, map_smul, smul_smul, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i), hT.isSymmetric.apply_eigenvectorBasis,
    RCLike.ofReal_eq_complex_ofReal]

lemma supportInverseRoot_mul_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * positiveRoot T hT = spectralSupport T hT := by
  rw [supportInverseRoot, positiveRoot, spectralSupport, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h
  · simp [h]
  · exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr
      (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm h)))

lemma root_mul_supportInverseRoot (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * supportInverseRoot T hT = spectralSupport T hT := by
  rw [supportInverseRoot, positiveRoot, basisDiagonal_mul]
  simp_rw [mul_comm (Real.sqrt _)]
  simpa only [supportInverseRoot, positiveRoot, basisDiagonal_mul] using
    supportInverseRoot_mul_root T hT

lemma supportInverseRoot_normalize (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * T * supportInverseRoot T hT = spectralSupport T hT := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [supportInverseRoot, spectralSupport, OrthonormalBasis.coe_toBasis,
    Module.End.mul_apply, basisDiagonal_apply_basis, map_smul,
    hT.isSymmetric.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal, smul_smul,
    ← Complex.ofReal_mul]
  congr 2
  split_ifs with h
  · simp [h]
  · have hs : Real.sqrt (hT.isSymmetric.eigenvalues rfl i) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm h))
    field_simp [hs]
    exact (Real.sq_sqrt (hT.nonneg_eigenvalues rfl i)).symm

lemma spectralSupport_idempotent (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    spectralSupport T hT * spectralSupport T hT = spectralSupport T hT := by
  rw [spectralSupport, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs <;> norm_num

lemma spectralSupport_mul (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    spectralSupport T hT * T = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [spectralSupport, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    hT.isSymmetric.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal, map_smul,
    basisDiagonal_apply_basis, smul_smul]
  split_ifs with h <;> simp [h]

def densityMean {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  (Fintype.card J : ℂ)⁻¹ • ∑ j, R j

omit [FiniteDimensional ℂ E] in
lemma densityMean_positive [FiniteDimensional ℂ E] {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E)
    (hR : ∀ j, (R j).IsPositive) : (densityMean R).IsPositive := by
  apply (LinearMap.isPositive_sum _ (fun j _ => hR j)).smul_of_nonneg
  rw [show (Fintype.card J : ℂ) = ((Fintype.card J : ℝ) : ℂ) by simp,
    ← Complex.ofReal_inv, Complex.nonneg_iff]
  exact ⟨inv_nonneg.mpr (Nat.cast_nonneg _), rfl⟩

omit [FiniteDimensional ℂ E] in
lemma densityMean_sum [FiniteDimensional ℂ E] {J : Type*} [Fintype J] [Nonempty J] (R : J → E →ₗ[ℂ] E) :
    ∑ j, R j = (Fintype.card J : ℂ) • densityMean R := by
  simp [densityMean, smul_smul, Fintype.card_ne_zero]

lemma normalizedDensity_positive {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) (j : J) :
    (supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR)).IsPositive := by
  have hp := (hR j).conj_adjoint
    (supportInverseRoot (densityMean R) (densityMean_positive R hR))
  rw [(supportInverseRoot_positive _ _).isSymmetric.adjoint_eq] at hp
  exact hp

lemma normalizedDensity_sum {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) :
    (∑ j, supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR)) =
      (Fintype.card J : ℂ) • spectralSupport (densityMean R) (densityMean_positive R hR) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, densityMean_sum R,
    mul_smul_comm, smul_mul_assoc, supportInverseRoot_normalize]

def densityCell {J : Type*} [Fintype J] (R : J → E →ₗ[ℂ] E)
    (hR : ∀ j, (R j).IsPositive) (S : E →ₗ[ℂ] E) (j : J) : ℝ :=
  (LinearMap.trace ℂ E
    (supportInverseRoot (densityMean R) (densityMean_positive R hR) * R j *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) * S)).re

lemma densityCell_nonneg {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (j : J) : 0 ≤ densityCell R hR S j :=
  positive_trace_product_nonneg _ _ (normalizedDensity_positive R hR j) hS

lemma densityCell_sum_le {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (htS : (LinearMap.trace ℂ E S).re = 1) :
    ∑ j, densityCell R hR S j ≤ Fintype.card J := by
  simp only [densityCell, ← Complex.re_sum, ← map_sum]
  rw [← Finset.sum_mul, normalizedDensity_sum R hR, smul_mul_assoc, map_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  have h := positive_projection_trace_le S
    (spectralSupport (densityMean R) (densityMean_positive R hR)) hS
    (spectralSupport_positive _ _).isSymmetric (spectralSupport_idempotent _ _)
  rw [LinearMap.trace_mul_comm, htS] at h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card J))

theorem normalized_density_product_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (W : Finset (A × B)) (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ∏ c ∈ W, densityCell R hR (S c.1) c.2 ≤ missingCellFactor W :=
  occupied_cell_product_bound W _ (fun i j => densityCell_nonneg R hR (S i) (hS i) j)
    (fun i => densityCell_sum_le R hR (S i) (hS i) (htS i))

lemma positiveRoot_quadratic (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = ‖positiveRoot T hT x‖ ^ 2 := by
  conv_lhs => rw [← positiveRoot_square T hT]
  rw [Module.End.mul_apply,
    ← (positiveRoot_positive T hT).isSymmetric]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma positive_quadratic_zero_iff (T : E →ₗ[ℂ] E) (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = 0 ↔ T x = 0 := by
  constructor
  · intro hz
    rw [positiveRoot_quadratic T hT, sq_eq_zero_iff, norm_eq_zero] at hz
    rw [← positiveRoot_square T hT, Module.End.mul_apply, hz, map_zero]
  · intro hz
    simp [hz]

lemma densityMean_kernel {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    {x : E} (hx : densityMean R x = 0) (j : J) : R j x = 0 := by
  have hsum : ∑ j, (inner ℂ x (R j x)).re = 0 := by
    rw [← Complex.re_sum, ← inner_sum, ← LinearMap.sum_apply, densityMean_sum R]
    simp [hx]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => (hR j).re_inner_nonneg_right x)).mp hsum j (Finset.mem_univ _)
  exact (positive_quadratic_zero_iff (R j) (hR j) x).mp hzero

lemma density_right_support {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) (j : J) :
    R j * spectralSupport (densityMean R) (densityMean_positive R hR) = R j := by
  apply ((densityMean_positive R hR).isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [spectralSupport, OrthonormalBasis.coe_toBasis, Module.End.mul_apply,
    basisDiagonal_apply_basis, map_smul]
  split_ifs with h
  · have hg : densityMean R ((densityMean_positive R hR).isSymmetric.eigenvectorBasis rfl i) = 0 := by
      simp only [(densityMean_positive R hR).isSymmetric.apply_eigenvectorBasis,
        h, RCLike.ofReal_zero, zero_smul]
    simp only [Complex.ofReal_zero, zero_smul, densityMean_kernel R hR hg j]
  · simp only [Complex.ofReal_one, one_smul]

lemma density_left_support {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) (j : J) :
    spectralSupport (densityMean R) (densityMean_positive R hR) * R j = R j := by
  have h := congrArg LinearMap.adjoint (density_right_support R hR j)
  simp only [← LinearMap.star_eq_adjoint, star_mul] at h
  simpa only [LinearMap.star_eq_adjoint,
    (spectralSupport_positive _ _).isSymmetric.adjoint_eq, (hR j).isSymmetric.adjoint_eq] using h

lemma norm_sq_le_positiveSquare_trace (T : E →ₗ[ℂ] E) :
    ‖T.toContinuousLinearMap‖ ^ 2 ≤ (LinearMap.trace ℂ E (positiveSquare T)).re := by
  have hp := adjoint_mul_positive T
  have htrace : 0 ≤ (LinearMap.trace ℂ E (positiveSquare T)).re :=
    Complex.re_le_re hp.trace_nonneg
  have hnorm : ‖T.toContinuousLinearMap‖ ≤
      Real.sqrt (LinearMap.trace ℂ E (positiveSquare T)).re := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro x hx
    have ho : Orthonormal ℂ (fun _ : Unit => x) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hij : i = j := Subsingleton.elim _ _
      simp [hij, inner_self_eq_norm_sq_to_K, hx]
    have hv := positive_orthonormal_trace_le (positiveSquare T) hp (fun _ : Unit => x) ho
    simp only [Finset.univ_unique, Finset.sum_singleton, positiveSquare,
      Module.End.mul_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow, Complex.ofReal_re] at hv
    exact (Real.le_sqrt (norm_nonneg _) htrace).mpr hv
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt htrace)

lemma densityCell_norm_bound {J : Type*} [Fintype J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : E →ₗ[ℂ] E) (hS : S.IsPositive) (j : J) :
    ‖(positiveRoot (R j) (hR j) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        positiveRoot S hS).toContinuousLinearMap‖ ^ 2 ≤ densityCell R hR S j := by
  apply (norm_sq_le_positiveSquare_trace _).trans_eq
  unfold densityCell positiveSquare
  simp only [← LinearMap.star_eq_adjoint, star_mul]
  simp only [LinearMap.star_eq_adjoint,
    (positiveRoot_positive _ _).isSymmetric.adjoint_eq,
    (supportInverseRoot_positive _ _).isSymmetric.adjoint_eq]
  rw [show positiveRoot S hS *
        (supportInverseRoot (densityMean R) (densityMean_positive R hR) * positiveRoot (R j) (hR j)) *
        (positiveRoot (R j) (hR j) * supportInverseRoot (densityMean R) (densityMean_positive R hR) *
          positiveRoot S hS) =
      positiveRoot S hS * (supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        (positiveRoot (R j) (hR j) * positiveRoot (R j) (hR j)) *
        supportInverseRoot (densityMean R) (densityMean_positive R hR) * positiveRoot S hS) by
      simp only [mul_assoc],
    positiveRoot_square, LinearMap.trace_mul_comm]
  simp only [mul_assoc]
  rw [positiveRoot_square]

theorem normalized_density_norm_product_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (W : Finset (A × B)) (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ∏ c ∈ W, ‖(positiveRoot (R c.2) (hR c.2) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        positiveRoot (S c.1) (hS c.1)).toContinuousLinearMap‖ ^ 2 ≤ missingCellFactor W := by
  apply (Finset.prod_le_prod₀ (fun c _ => sq_nonneg _) (fun c _ =>
    densityCell_norm_bound R hR (S c.1) (hS c.1) c.2)).trans
  exact normalized_density_product_bound W R hR S hS htS

end SignedSweeps
end

end OAI
