import OAI.Probability.SignedSweeps.ConvexTwirl
import OAI.Probability.SignedSweeps.Isotypic

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev MatrixHilbert (I : Type*) [Fintype I] := EuclideanSpace ℂ (I × I)

def matrixHilbertEquiv : Matrix I I ℂ ≃ₗ[ℂ] MatrixHilbert I where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  invFun x := fun i j => x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] in
lemma matrixHilbert_inner [DecidableEq I] (A B : Matrix I I ℂ) :
    inner ℂ (matrixHilbertEquiv A) (matrixHilbertEquiv B) =
      Matrix.trace (B * A.conjTranspose) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  rfl

lemma matrixHilbert_conj_inner (U : Matrix.unitaryGroup I ℂ) (A B : Matrix I I ℂ) :
    inner ℂ (matrixHilbertEquiv ((U : Matrix I I ℂ) * A * star (U : Matrix I I ℂ)))
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * B * star (U : Matrix I I ℂ))) =
      inner ℂ (matrixHilbertEquiv A) (matrixHilbertEquiv B) := by
  rw [matrixHilbert_inner, matrixHilbert_inner]
  simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  let u : Matrix I I ℂ := U
  have hu : u.conjTranspose * u = 1 := U.2.1
  change Matrix.trace ((u * B * u.conjTranspose) * (u * (A.conjTranspose * u.conjTranspose))) = _
  calc
    Matrix.trace ((u * B * u.conjTranspose) * (u * (A.conjTranspose * u.conjTranspose))) =
        Matrix.trace (u * B * (u.conjTranspose * u) * A.conjTranspose * u.conjTranspose) := by
      simp only [mul_assoc]
    _ = Matrix.trace (u * (B * A.conjTranspose) * u.conjTranspose) := by
      rw [hu, mul_one, mul_assoc u B A.conjTranspose]
    _ = Matrix.trace (B * A.conjTranspose) := by
      rw [Matrix.trace_mul_cycle, hu, one_mul]

def matrixConjugationIsometry (U : Matrix.unitaryGroup I ℂ) :
    MatrixHilbert I ≃ₗᵢ[ℝ] MatrixHilbert I := by
  let e : Matrix I I ℂ ≃ₗ[ℂ] Matrix I I ℂ :=
    (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) U).toAlgEquiv.toLinearEquiv
  let L : MatrixHilbert I ≃ₗ[ℂ] MatrixHilbert I :=
    matrixHilbertEquiv.symm.trans (e.trans matrixHilbertEquiv)
  refine ⟨L.restrictScalars ℝ, fun x => ?_⟩
  have hi := matrixHilbert_conj_inner U (matrixHilbertEquiv.symm x) (matrixHilbertEquiv.symm x)
  have hi' : inner ℂ (L x) (L x) = inner ℂ x x := by
    change inner ℂ
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * matrixHilbertEquiv.symm x * star (U : Matrix I I ℂ)))
      (matrixHilbertEquiv ((U : Matrix I I ℂ) * matrixHilbertEquiv.symm x * star (U : Matrix I I ℂ))) = _
    simpa only [LinearEquiv.apply_symm_apply] using hi
  have hr := congrArg Complex.re hi'
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

@[simp] lemma matrixConjugationIsometry_apply (U : Matrix.unitaryGroup I ℂ)
    (A : Matrix I I ℂ) :
    matrixConjugationIsometry U (matrixHilbertEquiv A) =
      matrixHilbertEquiv ((U : Matrix I I ℂ) * A * star (U : Matrix I I ℂ)) := rfl

def matrixConjugationAction {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ) :
    G →* (MatrixHilbert I ≃ₗᵢ[ℝ] MatrixHilbert I) where
  toFun g := matrixConjugationIsometry (ρ g)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixHilbertEquiv.surjective x
    simp
  map_mul' := by
    intro g h
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨A, rfl⟩ := matrixHilbertEquiv.surjective x
    simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, matrixConjugationIsometry_apply,
      Submonoid.coe_mul, star_mul, mul_assoc]

theorem exists_matrix_twirl {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    (A : Matrix I I ℂ) :
    ∃ B : Matrix I I ℂ,
      matrixHilbertEquiv B ∈ closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A) ∧
      ∀ g, B * (ρ g : Matrix I I ℂ) = (ρ g : Matrix I I ℂ) * B := by
  obtain ⟨y, hy, hinv⟩ := exists_invariant_in_closedOrbitHull
    (matrixConjugationAction ρ) (matrixHilbertEquiv A)
  refine ⟨matrixHilbertEquiv.symm y, by simpa using hy, fun g => ?_⟩
  have h := congrArg matrixHilbertEquiv.symm (hinv g)
  change (ρ g : Matrix I I ℂ) * matrixHilbertEquiv.symm y * star (ρ g : Matrix I I ℂ) =
    matrixHilbertEquiv.symm y at h
  have h' := congrArg (fun M : Matrix I I ℂ => M * (ρ g : Matrix I I ℂ)) h
  simpa only [mul_assoc, (ρ g).2.1, mul_one] using h'.symm

lemma matrix_twirl_mem {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    {S : Set (Matrix I I ℂ)} (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (horbit : ∀ g, (ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ) ∈ S) : B ∈ S := by
  let L : MatrixHilbert I →ₗ[ℝ] Matrix I I ℂ :=
    matrixHilbertEquiv.symm.toLinearMap.restrictScalars ℝ
  have hc : IsClosed (L ⁻¹' S) := hclosed.preimage L.continuous_of_finiteDimensional
  have hv : Convex ℝ (L ⁻¹' S) := hconvex.linear_preimage L
  apply closure_minimal (convexHull_min ?_ hv) hc hB
  rintro _ ⟨g, rfl⟩
  exact horbit g

omit [DecidableEq I] in
lemma isClosed_positive_matrices [DecidableEq I] :
    IsClosed {A : Matrix I I ℂ | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    fun_prop

omit [Fintype I] [DecidableEq I] in
lemma convex_positive_matrices [Fintype I] [DecidableEq I] :
    Convex ℝ {A : Matrix I I ℂ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

lemma matrix_twirl_positive {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (hA : A.PosSemidef) : B.PosSemidef := by
  apply matrix_twirl_mem ρ hB (S := {M : Matrix I I ℂ | M.PosSemidef})
    isClosed_positive_matrices convex_positive_matrices
  intro g
  exact hA.mul_mul_conjTranspose_same (ρ g : Matrix I I ℂ)

lemma matrix_twirl_trace {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (Q : Matrix I I ℂ) (hQ : ∀ g, Q * (ρ g : Matrix I I ℂ) = (ρ g : Matrix I I ℂ) * Q) :
    Matrix.trace (B * Q) = Matrix.trace (A * Q) := by
  let S : Set (Matrix I I ℂ) := {X | Matrix.trace (X * Q) = Matrix.trace (A * Q)}
  have hc : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hv : Convex ℝ S := by
    intro X hX Y hY a b _ _ hab
    change Matrix.trace (X * Q) = Matrix.trace (A * Q) at hX
    change Matrix.trace (Y * Q) = Matrix.trace (A * Q) at hY
    change Matrix.trace ((a • X + b • Y) * Q) = _
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, hX, hY]
    rw [← add_smul, hab, one_smul]
  apply matrix_twirl_mem ρ hB hc hv
  intro g
  change Matrix.trace (((ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ)) * Q) = _
  let u : Matrix I I ℂ := ρ g
  have hu : star u * u = 1 := (ρ g).2.1
  have hq : Q * u = u * Q := hQ g
  calc
    Matrix.trace ((u * A * star u) * Q) = Matrix.trace ((A * star u * Q) * u) := by
      rw [mul_assoc u A (star u), mul_assoc u (A * star u) Q, Matrix.trace_mul_comm]
    _ = Matrix.trace (A * (star u * (Q * u))) := by simp only [mul_assoc]
    _ = Matrix.trace (A * Q) := by rw [hq, ← mul_assoc (star u) u Q, hu, one_mul]

lemma matrix_twirl_submodule {G : Type*} [Group G] (ρ : G →* Matrix.unitaryGroup I ℂ)
    {A B : Matrix I I ℂ}
    (hB : matrixHilbertEquiv B ∈
      closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A))
    (S : Submodule ℂ (Matrix I I ℂ))
    (hS : ∀ g, (ρ g : Matrix I I ℂ) * A * star (ρ g : Matrix I I ℂ) ∈ S) : B ∈ S :=
  matrix_twirl_mem ρ hB S.closed_of_finiteDimensional (S.restrictScalars ℝ).convex hS

end SignedSweeps
end

end OAI
