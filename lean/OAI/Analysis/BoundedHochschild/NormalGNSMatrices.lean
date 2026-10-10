import OAI.Analysis.BoundedHochschild.NormalGNSRepresentation
import OAI.Analysis.BoundedHochschild.CompletelyBoundedRows

namespace OAI

/-! The faithful normal realization preserves every finite matrix norm.
In particular it preserves the complete bounds used in right averaging. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Entrywise realization is isometric at each finite matrix size. -/
theorem normalGNS_matrix_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (n : ℕ)
    (A : CStarMatrix (Fin n) (Fin n) M) :
    ‖A.map (normalGNSRepresentation e)‖ = ‖A‖ := by
  let π := CStarMatrix.mapₙₐ (n := Fin n) (normalGNSRepresentation e).toNonUnitalStarAlgHom
  have hπ : Function.Injective π :=
    CStarMatrix.map_injective (normalGNSRepresentation_injective e)
  exact NonUnitalStarAlgHom.norm_map π hπ A

/-- The concrete Hilbert-space realization has the same complete bound as
the original map. No extra regularity of that map is required. -/
theorem normalGNS_complete_bound_iff (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (C : ℝ) :
    CompletelyBoundedEstimate T C ↔ 0 ≤ C ∧
      ∀ (n : ℕ) (A : CStarMatrix (Fin n) (Fin n) M),
        ‖(A.map T).map (normalGNSRepresentation e)‖ ≤ C * ‖A‖ := by
  simp only [normalGNS_matrix_norm, CompletelyBoundedEstimate]

/-- The representation as a continuous linear map. -/
def normalGNSLinear (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    M →L[ℂ] (NormalGNS e →L[ℂ] NormalGNS e) :=
  (normalGNSRepresentation e).toLinearMap.mkContinuous 1 (fun a => by
    change ‖normalGNSRepresentation e a‖ ≤ 1 * ‖a‖
    rw [normalGNSRepresentation_norm, one_mul])

@[simp] lemma normalGNSLinear_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    normalGNSLinear e a = normalGNSRepresentation e a := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
