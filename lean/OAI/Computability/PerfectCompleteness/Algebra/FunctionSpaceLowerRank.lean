import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Algebra.LowerAffineSliceRank
import OAI.Computability.PerfectCompleteness.Algebra.ProductEvaluationRank
import OAI.Computability.PerfectCompleteness.Foundations.OddListExtraction

namespace OAI


namespace PerfectCompleteness.FunctionSpaceLowerRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PointwiseSpaces

section Transport

variable {K H V : Type*} [Field K]
  [AddCommGroup H] [Module K H] [AddCommGroup V] [Module K V]

def transportForm (e : H ≃ₗ[K] V) (F : H →ₗ[K] Module.Dual K H) :
    V →ₗ[K] Module.Dual K V :=
  e.symm.toLinearMap.dualMap.comp (F.comp e.symm.toLinearMap)

@[simp] theorem transportForm_apply (e : H ≃ₗ[K] V)
    (F : H →ₗ[K] Module.Dual K H) (u v : V) :
    transportForm e F u v = F (e.symm u) (e.symm v) := rfl

theorem transportForm_rank (e : H ≃ₗ[K] V) (F : H →ₗ[K] Module.Dual K H) :
    Module.finrank K (LinearMap.range (transportForm e F)) =
      Module.finrank K (LinearMap.range F) := by
  unfold transportForm
  rw [LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top F e.symm.range]
  exact e.symm.dualMap.finrank_map_eq (LinearMap.range F)

end Transport

section FunctionSpace

variable {Ω : Type*} (H : Submodule F2 (Ω → F2)) [FiniteDimensional F2 H]
  {ℓ m : Nat}

def matrixForm (F : H →ₗ[F2] Module.Dual F2 H) :
    Module.Dual F2 (Module.Dual F2 H) →ₗ[F2]
      Module.Dual F2 (Module.Dual F2 (Module.Dual F2 H)) :=
  transportForm (Module.evalEquiv F2 H) F

@[simp] theorem matrixForm_rank (F : H →ₗ[F2] Module.Dual F2 H) :
    Module.finrank F2 (LinearMap.range (matrixForm H F)) =
      Module.finrank F2 (LinearMap.range F) :=
  transportForm_rank (Module.evalEquiv F2 H) F

theorem testedGram_matrixForm (F : H →ₗ[F2] Module.Dual F2 H)
    (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2)) :
    LowerAffineSliceRank.testedGram (matrixForm H F) X =
      (fun i j => F (EvaluationMatrix.rows H X i) (EvaluationMatrix.rows H X j)) := rfl

theorem testedGram_multiplicationForm (z : Module.Dual F2 (squareSpace H))
    (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2)) :
    LowerAffineSliceRank.testedGram
        (matrixForm H (OddListExtraction.multiplicationForm H z)) X =
      (fun i j => z (OddListExtraction.productElement H
        (EvaluationMatrix.rows H X i) (EvaluationMatrix.rows H X j))) := rfl

end FunctionSpace


open MixedSupport CanonicalKeys
open ProductEvaluation (productSpan displayedJoint labelFunctional)

variable {n ℓ m : Nat} {Z Y : Type*} [Fintype Y]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  [FiniteDimensional F2 H]
  (other : Assignment slots → Z)
  (hone : (1 : Assignment slots → F2) ∈ squareSpace H)

def displayedRows (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (_ : Unit) (i : Fin ℓ) : Assignment slots → F2 :=
  (EvaluationMatrix.rows H X i).val

theorem displayedRows_products
    (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (c : Unit) (i j : Fin ℓ) :
    displayedRows slots H X c i * displayedRows slots H X c j ∈ squareSpace H :=
  mul_mem_squareSpace H (EvaluationMatrix.rows H X i).property
    (EvaluationMatrix.rows H X j).property

def testedProductSpan (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2)) :
    Submodule F2 (squareSpace H) :=
  productSpan (squareSpace H) (displayedRows slots H X) hone
    (displayedRows_products slots H X)

def IsLegalExtension (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (z : Module.Dual F2 (squareSpace H)) : Prop :=
  ∃ P : Label slots (displayedJoint (displayedRows slots H X) other),
    z.comp (testedProductSpan slots H hone X).subtype =
      labelFunctional slots (squareSpace H) (displayedRows slots H X) other hone
        (displayedRows_products slots H X) P

theorem legal_extension_tested_rank_le_one
    (X : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (z : Module.Dual F2 (squareSpace H))
    (hz : IsLegalExtension slots H other hone X z) :
    (LowerAffineSliceRank.testedGram
      (matrixForm H (OddListExtraction.multiplicationForm H z)) X).rank ≤ 1 := by
  obtain ⟨P, hP⟩ := hz
  rw [testedGram_multiplicationForm]
  exact ProductEvaluationRank.extension_productMatrix_rank_le_one slots
    (squareSpace H) (displayedRows slots H X) other hone
    (displayedRows_products slots H X) P z hP ()

variable [Fintype (Module.Dual F2 H)]
  [Fintype (Module.Dual F2 (Module.Dual F2 H))]
  [Fintype (Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))]
  [Fintype ((Fin ℓ → F2) →ₗ[F2] Module.Dual F2 H)]

theorem high_rank_agreement_lt_of_legal_extensions
    (f : (Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2)) → Option Y)
    (output : Y → Module.Dual F2 (squareSpace H))
    (legal : ∀ X y, f X = some y → IsLegalExtension slots H other hone X (output y))
    (r s : Nat) (ρ η : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ ℓ)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (MatrixErasure.erase f (fun X => ∃ y, f X = some y ∧
        OddListExtraction.formRank H (OddListExtraction.multiplicationForm H (output y)) ≤ s)) < η := by
  have tested : ∀ X y, f X = some y →
      (LowerAffineSliceRank.testedGram
        (matrixForm H (OddListExtraction.multiplicationForm H (output y))) X).rank ≤ 1 := by
    intro X y h
    exact legal_extension_tested_rank_le_one slots H other hone X (output y) (legal X y h)
  have h := LowerAffineSliceRank.high_rank_agreement_lt f
    (fun y => matrixForm H (OddListExtraction.multiplicationForm H (output y)))
    tested r s ρ η hm hρ hρ1 hconstants hrows herror
  simpa only [matrixForm_rank, OddListExtraction.formRank] using h

end
end PerfectCompleteness.FunctionSpaceLowerRank

end OAI
