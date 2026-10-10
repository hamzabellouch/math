import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.SchmidtRows

namespace OAI

/-! Bipartite quadratic energy and Schmidt weights. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.BipartiteEnergy
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.ModularMatrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def conjugateEntries (V : Matrix ι κ ℂ) : Matrix ι κ ℂ := V.map (starRingEnd ℂ)
def expectation (V : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) : ℂ :=
  bilinearExpectation (conjugateEntries V) A B

omit [DecidableEq ι] [DecidableEq κ] in
lemma bilinear_eq_trace (W : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    bilinearExpectation W A B = (A.transpose*(W*B*W.conjTranspose)).trace := by
  simp only [bilinearExpectation,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] in
lemma bilinear_left_mul (C : Matrix ι ι ℂ) (W : Matrix ι κ ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    bilinearExpectation (C*W) A B =
      bilinearExpectation W (C.transpose*A*C.conjTranspose.transpose) B := by
  rw [bilinear_eq_trace,bilinear_eq_trace,conjTranspose_mul]
  have hm : C*W*B*(W.conjTranspose*C.conjTranspose) =
      C*(W*B*W.conjTranspose)*C.conjTranspose := by simp only [Matrix.mul_assoc]
  rw [hm]
  simp only [transpose_mul,transpose_transpose]
  rw [← Matrix.mul_assoc,Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma conjugateEntries_mul (C : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) :
    conjugateEntries (C*V) = conjugateEntries C * conjugateEntries V := by
  exact Matrix.map_mul

omit [Fintype ι] [DecidableEq ι] in
lemma conjugateEntries_transpose (C : Matrix ι ι ℂ) :
    (conjugateEntries C).transpose = C.conjTranspose := rfl

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma conjugateEntries_conjTranspose (C : Matrix ι κ ℂ) :
    C.conjTranspose.map (starRingEnd ℂ) = (conjugateEntries C).conjTranspose := by
  ext i j
  simp [conjugateEntries,conjTranspose_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma conjugateEntries_gram (V : Matrix ι κ ℂ) :
    conjugateEntries V * (conjugateEntries V).conjTranspose =
      (V*V.conjTranspose).map (starRingEnd ℂ) := by
  rw [Matrix.map_mul,conjugateEntries_conjTranspose]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
lemma expectation_left_mul (C : Matrix ι ι ℂ) (V : Matrix ι κ ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    expectation (C*V) A B = expectation V (C.conjTranspose*A*C) B := by
  unfold expectation
  rw [conjugateEntries_mul,bilinear_left_mul,conjugateEntries_transpose]
  have hc : (conjugateEntries C).conjTranspose.transpose = C := by
    ext i j
    simp [conjugateEntries,conjTranspose_apply]
  rw [hc]

omit [Fintype ι] in
lemma conjugateEntries_diagonal (p : ι → ℝ) :
    (diagonal (fun i => (p i : ℂ))).map (starRingEnd ℂ) = diagonal (fun i => (p i : ℂ)) := by
  ext i j
  by_cases h : i=j <;> simp [h]

omit [DecidableEq κ] in
lemma gram_in_unitary_basis (V : Matrix ι κ ℂ) (U : unitary (Matrix ι ι ℂ))
    (p : ι → ℝ) (c : ℝ)
    (hV : V*V.conjTranspose = (c^2:ℂ) • ((U:Matrix ι ι ℂ)*diagonal (fun i => (p i:ℂ))*(U:Matrix ι ι ℂ).conjTranspose)) :
    conjugateEntries ((U:Matrix ι ι ℂ).conjTranspose*V) *
      (conjugateEntries ((U:Matrix ι ι ℂ).conjTranspose*V)).conjTranspose =
        (c^2:ℂ) • diagonal (fun i => (p i:ℂ)) := by
  rw [conjugateEntries_gram,conjTranspose_mul,conjTranspose_conjTranspose]
  have hu : (U:Matrix ι ι ℂ).conjTranspose*(U:Matrix ι ι ℂ)=1 := by
    exact Unitary.coe_star_mul_self U
  have hgram : (U:Matrix ι ι ℂ).conjTranspose*V*(V.conjTranspose*(U:Matrix ι ι ℂ)) =
      (c^2:ℂ) • diagonal (fun i => (p i:ℂ)) := by
    calc
      _ = (U:Matrix ι ι ℂ).conjTranspose*(V*V.conjTranspose)*(U:Matrix ι ι ℂ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hV,Matrix.mul_smul,Matrix.smul_mul]
        congr 1
        simp only [← Matrix.mul_assoc,hu,Matrix.one_mul]
        rw [Matrix.mul_assoc,hu,Matrix.mul_one]
  rw [hgram]
  ext i j
  by_cases h : i=j <;> simp [h,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply]

end PolynomialPEPS.Subvolume.BipartiteEnergy

namespace PolynomialPEPS.Subvolume.BipartiteEnergy
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.ModularMatrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def distortionInBasis (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) (p : ι → ℝ) (a : ℝ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U (distortion ((Unitary.conjStarAlgAut ℂ _ U).symm A) p a)

lemma distortionInBasis_eq (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) (p : ι → ℝ) (a : ℝ) :
    distortionInBasis U A p a =
      (1/2:ℂ) • (Unitary.conjStarAlgAut ℂ _ U (weightPower p a) * A *
          Unitary.conjStarAlgAut ℂ _ U (weightInverse p a) +
        Unitary.conjStarAlgAut ℂ _ U (weightInverse p a) * A *
          Unitary.conjStarAlgAut ℂ _ U (weightPower p a)) - A := by
  simp only [distortionInBasis,distortion,map_sub,map_smul,map_add,map_mul,
    StarAlgEquiv.apply_symm_apply]

omit [DecidableEq κ] in
lemma expectation_conjugate (U : unitary (Matrix ι ι ℂ)) (V : Matrix ι κ ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    expectation V (Unitary.conjStarAlgAut ℂ _ U A) B =
      expectation ((U:Matrix ι ι ℂ).conjTranspose*V) A B := by
  rw [expectation_left_mul,conjTranspose_conjTranspose]
  rfl

theorem basis_product_error_le (V : Matrix ι κ ℂ) (U : unitary (Matrix ι ι ℂ))
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (c : ℝ) (hc : 0 ≤ c)
    (hV : V*V.conjTranspose = (c^2:ℂ) • ((U:Matrix ι ι ℂ)*diagonal (fun i => (p i:ℂ))*(U:Matrix ι ι ℂ).conjTranspose))
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (a : ℝ) (ha : |a| ≤ 1/4) :
    ‖expectation V (distortionInBasis U A p a) B‖ ≤
      32*a^2*c^2*(∑ i, p i)*(‖A‖*‖B‖) := by
  rw [distortionInBasis,expectation_conjugate]
  have h := scaled_product_error_le (conjugateEntries ((U:Matrix ι ι ℂ).conjTranspose*V))
    p hp c hc (gram_in_unitary_basis V U p c hV)
    ((Unitary.conjStarAlgAut ℂ _ U).symm A) B a ha
  have hn : ‖(Unitary.conjStarAlgAut ℂ _ U).symm A‖ = ‖A‖ := by
    rw [Unitary.conjStarAlgAut_symm_apply,CStarRing.norm_mul_coe_unitary]
    exact CStarRing.norm_coe_unitary_mul (star U) A
  rw [hn] at h
  exact h

end PolynomialPEPS.Subvolume.BipartiteEnergy

end

end OAI
