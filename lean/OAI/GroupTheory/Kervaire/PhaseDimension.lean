import OAI.GroupTheory.Kervaire.PhaseFaithfulness

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- A basis adapted to a subspace and its orthogonal complement. -/
def orthogonalPairBasis (E : Submodule ℂ H) :
    Module.Basis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  ((stdOrthonormalBasis ℂ E).toBasis.prod (stdOrthonormalBasis ℂ Eᗮ).toBasis).map
    (E.prodEquivOfIsCompl Eᗮ E.isCompl_orthogonal)

@[simp] theorem orthogonalPairBasis_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairBasis E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem orthogonalPairBasis_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairBasis E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem orthogonalPairBasis_orthonormal (E : Submodule ℂ H) :
    Orthonormal ℂ (orthogonalPairBasis E) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa only [orthogonalPairBasis_inl, Submodule.coe_inner,
      Sum.inl.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal) i j
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact (stdOrthonormalBasis ℂ Eᗮ j).property _ (stdOrthonormalBasis ℂ E i).property
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact inner_eq_zero_symm.mp
      ((stdOrthonormalBasis ℂ Eᗮ i).property _ (stdOrthonormalBasis ℂ E j).property)
  · simpa only [orthogonalPairBasis_inr, Submodule.coe_inner,
      Sum.inr.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Eᗮ).orthonormal) i j

/-- The normalized basis is orthonormal. -/
def orthogonalPairONB (E : Submodule ℂ H) :
    OrthonormalBasis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  (orthogonalPairBasis E).toOrthonormalBasis (orthogonalPairBasis_orthonormal E)

@[simp] theorem orthogonalPairONB_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairONB E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

@[simp] theorem orthogonalPairONB_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairONB E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

end

section
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ H] in
/-- The sum of vector functionals over an ONB is precisely algebraic trace. -/
theorem vectorSum_onb (b : OrthonormalBasis ι ℂ H) (T : Operator H) :
    vectorSum b T = LinearMap.trace ℂ H T.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b, vectorSum_apply]
  rfl

/-- The spectral phase of a finite-dimensional unitary does not depend on ONB. -/
theorem sumPhase_onb_eq (U : Operator H) (hU : U ∈ unitary (Operator H))
    (b : OrthonormalBasis ι ℂ H) (c : OrthonormalBasis κ ℂ H) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U b = sumPhase U c := by
  apply sumPhase_eq_of_moments U U hU hU b c
  intro n
  rw [vectorSum_onb, vectorSum_onb]

/-- A unitary and its adjoint fix exactly the same vectors. -/
theorem star_fixed_of_fixed (U : Operator H) (hU : U ∈ unitary (Operator H))
    (v : H) (hv : U v = v) : star U v = v := by
  calc star U v = star U (U v) := by rw [hv]
       _ = (star U * U) v := rfl
       _ = v := by rw [(Unitary.mem_iff.mp hU).1]; rfl

/-- Inverse-pair phases are bounded by codimension of any common fixed space. -/
theorem sumPhase_add_star_le_codim (U : Operator H) (hU : U ∈ unitary (Operator H))
    (b : OrthonormalBasis ι ℂ H) (E : Submodule ℂ H)
    (hE : ∀ v : E, U (v : H) = (v : H)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    sumPhase U b + sumPhase (star U) b ≤ (Module.finrank ℂ Eᗮ : ℝ) := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
  change sumPhase U b + sumPhase (star U) b ≤ _
  rw [sumPhase_onb_eq U hU b (orthogonalPairONB E),
    sumPhase_onb_eq (star U) (Unitary.star_mem hU) b (orthogonalPairONB E)]
  unfold sumPhase
  rw [← Finset.sum_add_distrib, Fintype.sum_sum_type]
  have hz (i : Fin (Module.finrank ℂ E)) :
      vectorPhase U (orthogonalPairONB E (Sum.inl i)) +
        vectorPhase (star U) (orthogonalPairONB E (Sum.inl i)) = 0 := by
    rw [orthogonalPairONB_inl,
      vectorPhase_eq_zero_of_fixed U hU _ (hE _),
      vectorPhase_eq_zero_of_fixed (star U) (Unitary.star_mem hU) _
        (star_fixed_of_fixed U hU _ (hE _))]
    exact zero_add 0
  simp only [hz, Finset.sum_const_zero, zero_add]
  calc
    (∑ i : Fin (Module.finrank ℂ Eᗮ),
      (vectorPhase U (orthogonalPairONB E (.inr i)) +
       vectorPhase (star U) (orthogonalPairONB E (.inr i)))) ≤
        ∑ _i : Fin (Module.finrank ℂ Eᗮ), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [orthogonalPairONB_inr, Submodule.norm_coe,
        (stdOrthonormalBasis ℂ Eᗮ).norm_eq_one, one_pow] using
        vectorPhase_add_star_le U hU (orthogonalPairONB E (.inr i))
    _ = (Module.finrank ℂ Eᗮ : ℝ) := by simp

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

/-- Powers telescope under a unitary conjugation. -/
theorem unitary_conj_pow (U Q : Operator H) (hQ : Q ∈ unitary (Operator H)) (n : ℕ) :
    (Q * U * star Q)^n = Q * U^n * star Q := by
  induction n with
  | zero => simpa using (Unitary.mem_iff.mp hQ).2.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    have h := (Unitary.mem_iff.mp hQ).1
    calc (Q * U^n * star Q) * (Q * U * star Q) =
        Q * U^n * (star Q * Q) * U * star Q := by noncomm_ring
         _ = Q * (U^n * U) * star Q := by rw [h]; noncomm_ring

omit [FiniteDimensional ℂ H] in
/-- The finite-vector trace of an ONB is cyclic. -/
theorem vectorSum_onb_mul_comm (b : OrthonormalBasis ι ℂ H) (T S : Operator H) :
    vectorSum b (T*S) = vectorSum b (S*T) := by
  rw [vectorSum_onb, vectorSum_onb]
  exact LinearMap.trace_mul_comm ℂ T.toLinearMap S.toLinearMap

/-- Conjugation preserves the exact, possibly discontinuous, spectral phase. -/
theorem sumPhase_unitary_conj (U Q : Operator H)
    (hU : U ∈ unitary (Operator H)) (hQ : Q ∈ unitary (Operator H))
    (b : OrthonormalBasis ι ℂ H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ))
    sumPhase (Q*U*star Q) b = sumPhase U b := by
  apply sumPhase_eq_of_moments _ _
    (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ)) hU b b
  intro n
  rw [unitary_conj_pow U Q hQ n,
    vectorSum_onb_mul_comm b (Q * U^n) (star Q), ← mul_assoc,
    (Unitary.mem_iff.mp hQ).1, one_mul]

/-- Inverse-symmetric spectrum divides the codimension bound by two. -/
theorem sumPhase_le_half_codim (U Q : Operator H)
    (hU : U ∈ unitary (Operator H)) (hQ : Q ∈ unitary (Operator H))
    (hconj : Q*U*star Q = star U)
    (b : OrthonormalBasis ι ℂ H) (E : Submodule ℂ H)
    (hE : ∀ v : E, U (v : H) = (v : H)) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U b ≤ ((Module.finrank ℂ H : ℝ) - Module.finrank ℂ E) / 2 := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
  change sumPhase U b ≤ _
  have heq : sumPhase (star U) b = sumPhase U b := by
    simpa only [hconj] using sumPhase_unitary_conj U Q hU hQ b
  have hb := sumPhase_add_star_le_codim U hU b E hE
  change sumPhase U b + sumPhase (star U) b ≤ (Module.finrank ℂ Eᗮ : ℝ) at hb
  rw [heq] at hb
  have hd : (Module.finrank ℂ E : ℝ) + Module.finrank ℂ Eᗮ = Module.finrank ℂ H := by
    exact_mod_cast E.finrank_add_finrank_orthogonal
  linarith

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

omit [Group A] in
@[simp] theorem scalarTensor_pow (M : Matrix D D ℂ) (n : ℕ) :
    scalarTensor (A := A) (M^n) = scalarTensor M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, scalarTensor_mul, ih, pow_succ]

omit [Group A] in
/-- The ordinary finite-dimensional operator trace has the matrix entries used
by the amplification trace; no normalization is introduced here. -/
theorem vectorSum_toEuclideanCLM (M : Matrix D D ℂ) :
    vectorSum (EuclideanSpace.basisFun D ℂ) ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) M) = Matrix.trace M := by
  classical
  rw [vectorSum_onb]
  change LinearMap.trace ℂ (EuclideanSpace ℂ D) (Matrix.toEuclideanLin M) = _
  rw [LinearMap.trace_eq_matrix_trace _ (EuclideanSpace.basisFun D ℂ).toBasis]
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- The cut-sensitive phase of a scalar amplification is the ordinary
finite-dimensional phase, proved through every nonnegative power moment. -/
theorem phase_scalarTensor (M : Matrix D D ℂ) (hM : M ∈ Matrix.unitaryGroup D ℂ) :
    let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
    let _ := isStarNormal_of_mem_unitary (Unitary.map_mem (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) hM)
    KervaireMatrix.phase (scalarTensor (A := A) M) =
      sumPhase ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) M) (EuclideanSpace.basisFun D ℂ) := by
  classical
  apply sumPhase_eq_of_moments _ _ (scalarTensor_mem_unitary (A := A) hM)
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) hM)
    (fun i : D => delta (i,(1 : A))) (EuclideanSpace.basisFun D ℂ)
  intro n
  rw [← trace_eq_vectorSum, ← scalarTensor_pow, trace_scalarTensor,
    ← map_pow, vectorSum_toEuclideanCLM]

end KervaireMatrix

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

/-- A scalar point of the spectrum of an involution is exactly a sign. -/
theorem spectrum_involution {U : Operator H} (hU : U ^ 2 = 1) (z : spectrum ℂ U) :
    (z : ℂ) = 1 ∨ (z : ℂ) = -1 := by
  have hz : (z : ℂ)^2 ∈ spectrum ℂ (U^2) := by
    rw [spectrum.map_pow]
    exact ⟨z,z.property,rfl⟩
  rw [hU] at hz
  exact sq_eq_one_iff.mp (by simpa using hz)

/-- Spectral phase on a self-adjoint unitary is one half of its negative projection. -/
theorem vectorPhase_involution (U : Operator H) (hU : U ∈ unitary (Operator H))
    (hUU : U ^ 2 = 1) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = ((vectorCLM ξ 1).re - (vectorCLM ξ U).re) / 4 := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℝ) :=
    ⟨fun z => (1 - (z : ℂ).re) / 4,
      (continuous_const.sub (Complex.continuous_re.comp continuous_subtype_val)).div_const _⟩
  have he : (fun z : spectrum ℂ U => phase z) = f := by
    funext z
    rcases spectrum_involution hUU z with hz | hz
    · simp [f, phase, hz]
    · simp only [f, ContinuousMap.coe_mk, hz, phase, Complex.arg_neg_one]
      rw [show Real.pi / (2 * Real.pi) = (1/2 : ℝ) by field_simp]
      norm_num [Int.fract_eq_self.mpr (by norm_num : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) < 1)]
  have hf : complexify f = (1 / 4 : ℂ) •
      (1 - (ContinuousMap.id ℂ).restrict (spectrum ℂ U)) := by
    ext z
    rcases spectrum_involution hUU z with hz | hz <;>
      simp [complexify, f, hz]; norm_num
  change (∫ z, phase z ∂vectorMeasure U ξ) = _
  rw [he, integral_vectorMeasure, hf, map_smul, map_sub, map_one, cfcHom_id]
  simp [Complex.sub_re, Complex.mul_re]
  ring

/-- The unnormalized matrix version used for the involution SJ. -/
theorem sumPhase_involution {ι : Type*} [Fintype ι]
    (U : Operator H) (hU : U ∈ unitary (Operator H)) (hUU : U ^ 2 = 1) (ξ : ι → H) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U ξ = ((vectorSum ξ 1).re - (vectorSum ξ U).re) / 4 := by
  let _ := isStarNormal_of_mem_unitary hU
  unfold sumPhase
  simp only [vectorPhase_involution U hU hUU, vectorSum_apply, Complex.re_sum,
    ]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

end KervaireSpectral

end

end OAI
