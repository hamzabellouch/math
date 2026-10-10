import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeVectorAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SmoothVectorActionLattice

namespace OAI

/-! # Uniform solvable Lie lattices for split integral-abelian extensions -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)
include C

theorem abelian_extension_finiteIndex_lattice {n : ℕ}
    (ρ : IntegralLatticeGroup n →* MulAut H) :
    ∃ Γ : Subgroup (H ⋊[ρ] IntegralLatticeGroup n), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨m, hm, φ, hφ, he⟩ := C.exists_vector_action ρ
  obtain ⟨S, Λ, hΛ, ⟨e⟩⟩ := smooth_vectorAction_integral_lattice φ hφ
    (ρ.comp (latticePowerHom n m)) C.lattice C.uniform C.equiv he
  let F := integralSemidirectPowerMap ρ m
  have hF : Function.Injective F := integralSemidirectPowerMap_injective ρ hm
  let eF : (H ⋊[ρ.comp (latticePowerHom n m)] IntegralLatticeGroup n) ≃* F.range :=
    MulEquiv.ofBijective F.rangeRestrict
      ⟨fun _ _ h => hF (congrArg Subtype.val h), F.rangeRestrict_surjective⟩
  exact ⟨F.range, integralSemidirectPowerMap_finiteIndex ρ hm, S, Λ, hΛ, ⟨eF.symm.trans e⟩⟩

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
