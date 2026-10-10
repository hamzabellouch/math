import OAI.Geometry.NodalSets.Elliptic.RealMatrixEntryPerturbation

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

theorem real_ellipticity_neighborhood (Q : Set Yau.Jets.Coord)
    (C₀ : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (k L : ℝ) (hk : 0 < k)
    (hlo : ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C₀ x i j*z j)
    (hhi : ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      (∑ i, ∑ j, z i*C₀ x i j*z j) ≤ L*(∑ i, z i^2))
    (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hclose : ∀ x ∈ Q, ∀ i j, |C x i j-C₀ x i j| ≤ k/32) :
    ∀ x ∈ Q, ∀ z : Yau.Jets.Coord,
      (k/2)*(∑ i, z i^2) ≤ (∑ i, ∑ j, z i*C x i j*z j) ∧
      (∑ i, ∑ j, z i*C x i j*z j) ≤ (L+k/2)*(∑ i, z i^2) := by
  intro x hx z
  have h := real_matrix_entry_perturbation (C x) (C₀ x) (k/32) (by positivity) (hclose x hx) z
  obtain ⟨h₁,h₂⟩ := abs_le.mp h
  constructor <;> nlinarith only [h₁,h₂,hlo x hx z,hhi x hx z]

end
end Yau.Geometry

end OAI
