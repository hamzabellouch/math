import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentByAbelianRealization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicExtensionDimension

namespace OAI

/-! # The lattice-realization consequence of Dekimpe's theorem

All extensions used here are actual group extensions.  The nilshadow
construction supplies the connected Lie model without a splitting premise.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

theorem IsPolycyclic.exists_solvable_finiteDimension {G : Type} [Group G]
    (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H ∧
      HasFiniteIntegralCohomologicalDimension H := by
  let B : Subgroup G := ⊥
  let : Group.FG B := finitelyGenerated_of_isCyclic
  have hB : ∃ V : Subgroup B, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
    let V : Subgroup B := ⊤
    let : Group.IsSolvable V := Group.isSolvable_of_comm (fun _ _ => Subsingleton.elim _ _)
    exact ⟨V, inferInstance, inferInstance,
      (poincareDuality_zero_of_subsingleton V).finiteCohomologicalDimension V⟩
  exact exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient B hB
    (hG.of_surjective (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)).isVirtuallyPolycyclic

theorem virtuallyPolycyclic_uniform_lattice {G : Type} [Group G]
    (hG : IsVirtuallyPolycyclic G) :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  obtain ⟨P, hPi, hP⟩ := hG
  let := hPi
  apply uniform_lattice_realization_of_finiteIndex P
  obtain ⟨H, hHi, hHs, hHcd⟩ := hP.exists_solvable_finiteDimension
  let := hHi
  let := hHs
  apply uniform_lattice_realization_of_finiteIndex H
  obtain ⟨V, hVn, hVi, N, hNn, hNnil, hQ⟩ :=
    exists_finiteIndex_nilpotent_by_abelian hHcd
  let := hVi
  let := hNn
  let := hNnil
  let := hQ
  apply uniform_lattice_realization_of_finiteIndex V
  have hVpoly : IsPolycyclic V :=
    (hP.of_injective H.subtype Subtype.val_injective).of_injective V.subtype Subtype.val_injective
  exact nilpotent_by_abelian_uniform_lattice hVpoly (hHcd.subgroup V).torsionFree N

/-- Dekimpe's lattice-realization conclusion follows from nilpotent completion
and the invariant graph construction. -/
theorem dekimpeLatticeRealizationInput : DekimpeLatticeRealizationInput := by
  intro G _ hG
  obtain ⟨K, hK, S, Λ, hΛ, e⟩ := virtuallyPolycyclic_uniform_lattice hG
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  exact ⟨K, hK, S, Λ, hΛ.1, hΛ.compactSpace_quotient, e⟩

end PolycyclicRecognition

end

end OAI
