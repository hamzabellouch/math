import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

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

theorem allocatedKernelRoot_le_budget (x : G → IntegerScalarCubeBox Empty S.value) (g : G) :
    |((x g none : ℤ) : ℝ)| ≤ allocatedPhysicalRootBudget B U basis S (fun _ => 0) := by
  let y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U basis S) :=
    fun j => integerScalarCubeBoxZero Empty (allocatedPrincipalSides B U basis S j)
      (allocatedPrincipalSides_pos B U basis S j)
  simpa only [allocatedPhysicalCubeRoot, Sum.elim_inl, zero_add] using
    allocatedPhysicalCube_root_budget B U basis S (fun _ => 0) x y (.inl g)

theorem allocatedKernelRoot_budget (x : G → IntegerScalarCubeBox Empty S.value) (g : G) :
    |((x g none : ℤ) : ℝ)| ≤ 1 + allocatedPhysicalRootBudget B U basis S (fun _ => 0) := by
  have hb := allocatedKernelRoot_le_budget B U basis S x g
  linarith

end Erdos3.VectorPolynomial

end

end OAI
