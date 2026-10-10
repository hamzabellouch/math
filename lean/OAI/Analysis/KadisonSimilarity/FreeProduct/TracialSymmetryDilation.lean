import OAI.Analysis.BoundedHochschild.MatrixDilation

namespace OAI

/-! Centered symmetry tests for contractions. The selfadjoint two-by-two
dilation has opposite diagonal entries, so its normalized trace vanishes
for every linear functional. Applying it to the selfadjoint off-diagonal
matrix of an arbitrary contraction yields a four-by-four symmetry with
the original contraction as one entry. This avoids any extra spectral
trace-equality hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder Matrix
open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A]

/-- The normalized two-by-two matrix extension of a linear functional. -/
def linearMatrixTrace (τ : A →ₗ[ℂ] ℂ) : Mat A →ₗ[ℂ] ℂ where
  toFun X := (τ (X 0 0) + τ (X 1 1)) / 2
  map_add' X Y := by simp only [CStarMatrix.add_apply, map_add]; ring
  map_smul' c X := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem linearMatrixTrace_apply (τ : A →ₗ[ℂ] ℂ) (X : Mat A) :
    linearMatrixTrace τ X = (τ (X 0 0) + τ (X 1 1)) / 2 := rfl

variable [PartialOrder A] [StarOrderedRing A]

local instance : NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ A := CStarAlgebra.instNonnegSpectrumClass

/-- The two-by-two symmetry associated to a selfadjoint contraction. -/
def selfAdjointSymmetryDilation (a : A) : Mat A :=
  diag (CFC.sqrt (1 - a ^ 2)) (-CFC.sqrt (1 - a ^ 2)) + offdiag a a

@[simp] theorem selfAdjointSymmetryDilation_entry (a : A) :
    selfAdjointSymmetryDilation a 0 1 = a := by
  simp [selfAdjointSymmetryDilation, diag, offdiag]

theorem selfAdjointSymmetryDilation_star (a : A) (ha : IsSelfAdjoint a) :
    star (selfAdjointSymmetryDilation a) = selfAdjointSymmetryDilation a := by
  have hr := (CFC.sqrt_nonneg (1 - a ^ 2)).isSelfAdjoint.star_eq
  simp only [selfAdjointSymmetryDilation, star_add, star_diag, star_offdiag,
    star_neg, hr, ha.star_eq]

theorem selfAdjoint_defect_nonneg (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    0 ≤ 1 - a ^ 2 := by
  have hsq : 0 ≤ a ^ 2 := by
    simpa only [ha.star_eq, pow_two] using star_mul_self_nonneg a
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ hsq,
    pow_two, ha.norm_mul_self]
  exact (sq_le_one_iff₀ (norm_nonneg a)).mpr hn

theorem selfAdjoint_defect_sqrt_commutes (a : A) :
    Commute (CFC.sqrt (1 - a ^ 2)) a := by
  have hc : Commute (1 - a ^ 2) a := by
    show (1 - a ^ 2) * a = a * (1 - a ^ 2)
    noncomm_ring
  simpa only [CFC.sqrt] using hc.cfcₙ_nnreal NNReal.sqrt

theorem selfAdjointSymmetryDilation_sq (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    selfAdjointSymmetryDilation a * selfAdjointSymmetryDilation a = 1 := by
  have hr := CFC.sqrt_mul_sqrt_self (1 - a ^ 2) (selfAdjoint_defect_nonneg a ha hn)
  have hc := (selfAdjoint_defect_sqrt_commutes a).eq
  simp only [pow_two] at hr hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [selfAdjointSymmetryDilation, CStarMatrix.mul_apply, Fin.sum_univ_two,
      diag, offdiag, hr, hc, pow_two]

/-- The symmetry as an actual unitary, with no existence assumption. -/
def selfAdjointSymmetryUnitary (a : A) (ha : IsSelfAdjoint a) (hn : ‖a‖ ≤ 1) :
    unitary (Mat A) :=
  ⟨selfAdjointSymmetryDilation a, by
    rw [Unitary.mem_iff]
    simp only [selfAdjointSymmetryDilation_star a ha, selfAdjointSymmetryDilation_sq a ha hn,
      and_self]⟩

/-- Opposite diagonal entries make the dilation centered without any
centering condition on its input. -/
theorem linearMatrixTrace_selfAdjointSymmetryDilation (τ : A →ₗ[ℂ] ℂ) (a : A) :
    linearMatrixTrace τ (selfAdjointSymmetryDilation a) = 0 := by
  simp [linearMatrixTrace, selfAdjointSymmetryDilation, diag, offdiag]

/-- A centered four-by-four symmetry containing an arbitrary contraction.
The blocks use the existing selfadjoint off-diagonal contraction lemma. -/
def contractionSymmetryUnitary (a : A) (ha : ‖a‖ ≤ 1) : unitary (Mat (Mat A)) :=
  selfAdjointSymmetryUnitary (offdiag a (star a)) (offdiag_selfAdjoint a)
    (offdiag_norm_le_one a ha)

theorem contractionSymmetryUnitary_star (a : A) (ha : ‖a‖ ≤ 1) :
    star (contractionSymmetryUnitary a ha : Mat (Mat A)) = contractionSymmetryUnitary a ha :=
  selfAdjointSymmetryDilation_star _ (offdiag_selfAdjoint a)

theorem contractionSymmetryUnitary_sq (a : A) (ha : ‖a‖ ≤ 1) :
    (contractionSymmetryUnitary a ha : Mat (Mat A)) * contractionSymmetryUnitary a ha = 1 :=
  selfAdjointSymmetryDilation_sq _ (offdiag_selfAdjoint a) (offdiag_norm_le_one a ha)

@[simp] theorem contractionSymmetryUnitary_entry (a : A) (ha : ‖a‖ ≤ 1) :
    (contractionSymmetryUnitary a ha : Mat (Mat A)) 0 1 0 1 = a := by
  change (selfAdjointSymmetryDilation (offdiag a (star a))) 0 1 0 1 = a
  rw [selfAdjointSymmetryDilation_entry]
  rfl

theorem linearMatrixTrace_contractionSymmetryUnitary (τ : A →ₗ[ℂ] ℂ)
    (a : A) (ha : ‖a‖ ≤ 1) :
    linearMatrixTrace (linearMatrixTrace τ)
      (contractionSymmetryUnitary a ha : Mat (Mat A)) = 0 :=
  linearMatrixTrace_selfAdjointSymmetryDilation _ _

theorem exists_centered_symmetry_dilation [Nontrivial A] (τ : A →ₗ[ℂ] ℂ)
    (a : A) (ha : ‖a‖ ≤ 1) :
    ∃ S : Mat (Mat A), star S = S ∧ S * S = 1 ∧ ‖S‖ ≤ 1 ∧
      linearMatrixTrace (linearMatrixTrace τ) S = 0 ∧ S 0 1 0 1 = a := by
  refine ⟨contractionSymmetryUnitary a ha, contractionSymmetryUnitary_star a ha,
    contractionSymmetryUnitary_sq a ha, ?_,
    linearMatrixTrace_contractionSymmetryUnitary τ a ha, contractionSymmetryUnitary_entry a ha⟩
  exact (CStarRing.norm_coe_unitary _).le

end KadisonSimilarity

end

end OAI
