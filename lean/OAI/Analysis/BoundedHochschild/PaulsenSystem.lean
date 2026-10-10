import OAI.Analysis.BoundedHochschild.ScalarPositiveBlocks
import OAI.Analysis.BoundedHochschild.OperatorSystemMatrices

namespace OAI

/-! The unital two-by-two operator system associated to a linear map. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def starConjugateLinear (T : A →ₗ[ℂ] B) : A →ₗ[ℂ] B where
  toFun a := star (T (star a))
  map_add' a b := by simp
  map_smul' z a := by simp

def paulsenSystem (A : Type*) [CStarAlgebra A] : Submodule ℂ (Mat A) where
  carrier := {X | ∃ z w : ℂ, X 0 0 = algebraMap ℂ A z ∧ X 1 1 = algebraMap ℂ A w}
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro X Y ⟨z, w, hz, hw⟩ ⟨z', w', hz', hw'⟩
    exact ⟨z + z', w + w', by simp only [CStarMatrix.add_apply, map_add, hz, hz'],
      by simp only [CStarMatrix.add_apply, map_add, hw, hw']⟩
  smul_mem' := by
    rintro c X ⟨z, w, hz, hw⟩
    refine ⟨c * z, c * w, ?_, ?_⟩
    · simp only [CStarMatrix.smul_apply, hz, Algebra.smul_def, map_mul]
    · simp only [CStarMatrix.smul_apply, hw, Algebra.smul_def, map_mul]

lemma paulsenSystem_one : (1 : Mat A) ∈ paulsenSystem A := by
  exact ⟨1, 1, by simp, by simp⟩

lemma paulsenSystem_star (X : Mat A) (hX : X ∈ paulsenSystem A) :
    star X ∈ paulsenSystem A := by
  obtain ⟨z, w, hz, hw⟩ := hX
  refine ⟨star z, star w, ?_, ?_⟩
  · change star (X 0 0) = _
    rw [hz]
    exact (map_star (StarAlgHom.ofId ℂ A) z).symm
  · change star (X 1 1) = _
    rw [hw]
    exact (map_star (StarAlgHom.ofId ℂ A) w).symm

def paulsenLinear (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : Mat A →ₗ[ℂ] Mat B where
  toFun X := CStarMatrix.ofMatrix !![
    algebraMap ℂ B (f (X 0 0)), T (X 0 1);
    starConjugateLinear T (X 1 0), algebraMap ℂ B (f (X 1 1))]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one, smul_smul]

def paulsenSystemMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : paulsenSystem A →ₗ[ℂ] Mat B :=
  (paulsenLinear f T).comp (paulsenSystem A).subtype

lemma paulsenSystemMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B) :
    paulsenSystemMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [paulsenSystemMap, paulsenLinear, starConjugateLinear, hf]

end BoundedHochschild.KadisonRingrose

end

end OAI
