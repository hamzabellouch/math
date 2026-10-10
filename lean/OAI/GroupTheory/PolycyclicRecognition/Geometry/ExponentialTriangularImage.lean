import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialKernel

namespace OAI

/-! # Global triangularity from exponential factor coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

theorem upperTriangular_of_exponential_factors {Γ X Y : Type*} [Group Γ] {m : ℕ}
    (f : X × Y → Γ) (hf : Function.Surjective f)
    (P : X → Matrix (Fin m) (Fin m) ℝ) (Q : Y → Matrix (Fin m) (Fin m) ℝ)
    (hP : ∀ x, (P x).IsUpperTriangular) (hQ : ∀ y, (Q y).IsUpperTriangular)
    (ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
    (he : ∀ x y, ρ (f (x,y)) = algebraExpUnit (P x) * algebraExpUnit (Q y)) :
    ∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular := by
  intro g
  obtain ⟨⟨x,y⟩,rfl⟩ := hf g
  rw [he]
  exact (positiveTriangularExp (P x) (hP x) * positiveTriangularExp (Q y) (hQ y)).property.1

end PolycyclicRecognition

end

end OAI
