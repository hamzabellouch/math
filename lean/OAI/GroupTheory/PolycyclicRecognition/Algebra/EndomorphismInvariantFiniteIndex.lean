import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicFiniteIndex
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Endomorphism-invariant finite-index refinements

The finite-target-kernel construction is invariant under every endomorphism,
not just automorphisms. This supplies the stable torsion-free subgroup needed
when passing from a virtually nilpotent base to an ascending extension.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G F : Type*} [Group G] [Group F]

theorem finiteTargetKernel_map_le (f : G →* G) :
    (finiteTargetKernel G F).map f ≤ finiteTargetKernel G F := by
  rintro _ ⟨g, hg, rfl⟩
  apply Subgroup.mem_iInf.mpr
  intro h
  exact Subgroup.mem_iInf.mp hg (h.comp f)

theorem exists_endomorphismInvariant_finiteIndex_le [Group.FG G]
    (H : Subgroup G) [H.FiniteIndex] :
    ∃ K : Subgroup G, K ≤ H ∧ K.FiniteIndex ∧
      ∀ f : G →* G, K.map f ≤ K := by
  let F := Equiv.Perm (G ⧸ H)
  refine ⟨finiteTargetKernel G F, ?_, finiteTargetKernel_finiteIndex,
    fun f => finiteTargetKernel_map_le f⟩
  intro g hg
  have he : MulAction.toPermHom G (G ⧸ H) g = 1 :=
    Subgroup.mem_iInf.mp hg (MulAction.toPermHom G (G ⧸ H))
  have hx := congrArg (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk g⁻¹)) he
  change QuotientGroup.mk (g * g⁻¹) = QuotientGroup.mk g⁻¹ at hx
  rw [mul_inv_cancel] at hx
  simpa using QuotientGroup.eq.mp hx.symm

theorem IsPolycyclic.exists_endomorphismInvariant_torsionFree_finiteIndex
    {G : Type} [Group G] (hG : IsPolycyclic G) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ HasNoNontrivialTorsion K ∧
      ∀ f : G →* G, K.map f ≤ K := by
  let : Group.FG G := hG.finitelyGenerated
  obtain ⟨H, hH, ht⟩ := hG.exists_torsionFree_finiteIndex
  let := hH
  obtain ⟨K, hKH, hK, hstable⟩ := exists_endomorphismInvariant_finiteIndex_le H
  exact ⟨K, hK, ht.of_injective (Subgroup.inclusion hKH)
    (Subgroup.inclusion_injective hKH), hstable⟩

end PolycyclicRecognition

end

end OAI
