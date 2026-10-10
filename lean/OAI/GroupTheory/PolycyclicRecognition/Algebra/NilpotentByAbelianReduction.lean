import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualNilpotentByAbelian

namespace OAI

/-! # The concrete nilpotent-by-abelian subgroup for the duality endgame -/

noncomputable section
namespace PolycyclicRecognition

theorem nilpotent_of_injective_hom {A B : Type*} [Group A] [Group B] [Group.IsNilpotent B]
    (f : A →* B) (hf : Function.Injective f) : Group.IsNilpotent A := by
  let e := MonoidHom.ofInjective hf
  exact Group.nilpotent_of_mulEquiv e.symm

theorem exists_finiteIndex_nilpotent_by_abelian
    {G : Type} [Group G] [Group.IsSolvable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ N : Subgroup H, ∃ _ : N.Normal, Group.IsNilpotent N ∧ IsMulCommutative (H ⧸ N) := by
  obtain ⟨F, hFn, hF, H, hHn, hHi, hcomm⟩ :=
    exists_nilpotent_normal_finiteIndex_commutator hG
  let := hFn
  let := hF
  let N := F.comap H.subtype
  let f : N →* F := (H.subtype.comp N.subtype).codRestrict F (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : F => (x : G)) hab
  have hN : Group.IsNilpotent N := nilpotent_of_injective_hom f hf
  have hc : commutator H ≤ N := by
    intro a ha
    exact hcomm ⟨a, ha, rfl⟩
  exact ⟨H, hHn, hHi, N, inferInstance, hN,
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hc⟩

end PolycyclicRecognition

end

end OAI
