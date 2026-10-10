import OAI.Analysis.BoundedHochschild.PaulsenPositivity
import OAI.Analysis.BoundedHochschild.UnitalPositiveExtension

namespace OAI

/-! Extend the two-by-two operator-system map into operators on the doubled
Hilbert space, using the proved positive extension theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertDouble (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : Fin 2 => H)

abbrev doubleMatrixHom : Mat (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  WeakPureInfiniteness.matrixOperatorHom (n := Fin 2) (H := H)

lemma matrixDouble_one :
    doubleMatrixHom (H := H) (1 : Mat (H →L[ℂ] H)) = 1 := by
  ext ξ i
  change (∑ j : Fin 2, (1 : Mat (H →L[ℂ] H)) i j (ξ j)) = ξ i
  fin_cases i <;> simp [CStarMatrix.one_apply, apply_ite]

def paulsenOperatorMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenSystem A →ₗ[ℂ] (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  (doubleMatrixHom (H := H) : Mat (H →L[ℂ] H) →ₗ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H)).comp (paulsenSystemMap f T)

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsenOperatorMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenOperatorMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  change doubleMatrixHom (H := H)
    (paulsenSystemMap f T ⟨1, paulsenSystem_one⟩) = 1
  rw [paulsenSystemMap_one f hf, matrixDouble_one]

variable [Nontrivial A]

lemma paulsenOperatorMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenOperatorMap f T) n X := by
  have h := paulsenSystemMap_positive f hf T hT n X hX
  exact map_nonneg (CStarMatrix.mapₙₐ (doubleMatrixHom (H := H))) h

theorem exists_paulsen_extension [Nontrivial H] (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖) :
    ∃ Φ : CompletelyPositiveMap (Mat A) (HilbertDouble H →L[ℂ] HilbertDouble H),
      Φ 1 = 1 ∧ ∀ X : paulsenSystem A, Φ (X : Mat A) = paulsenOperatorMap f T X := by
  obtain ⟨Φ, hΦ, _, hrest⟩ := exists_unital_completelyPositive_extension (paulsenSystem A)
    paulsenSystem_one paulsenSystem_star (paulsenOperatorMap f T)
    (paulsenOperatorMap_one f hf T) (paulsenOperatorMap_positive f hf T hT)
  exact ⟨Φ, hΦ, hrest⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
