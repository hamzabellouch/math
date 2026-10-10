import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalDir_smallness_forces_one
    (j : PrincipalTupleIndex
      (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val))
    {ξ : ℝ} (hξ : ξ ≤ 1)
    (hdir : ∀ t, (allocatedPrincipalSides B U basis S t : ℝ) ≤ ξ * S.value) :
    ξ = 1 := by
  have h := hdir ⟨j.1.val, j.2⟩
  have hs : allocatedPrincipalSides B U basis S ⟨j.1.val, j.2⟩ = S.value :=
    allocatedPrincipalSides_long B U basis S j.1.val j.1.property j.2.1 j.2.2
  rw [hs] at h
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  apply le_antisymm hξ
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI
