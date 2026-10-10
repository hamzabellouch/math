import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootGeneratorHomExt

namespace OAI

/-! # A nilpotent normal subgroup has a finite centralizer test -/

noncomputable section
namespace PolycyclicRecognition

theorem nilpotent_normal_centralizer_finite_test {G : Type} [Group G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (hN : HasFiniteIntegralCohomologicalDimension N) :
    ∃ S : Set G, S.Finite ∧ S ⊆ N ∧
      Subgroup.centralizer S = Subgroup.centralizer (N : Set G) := by
  obtain ⟨S, hS, hdet⟩ := nilpotent_exists_finite_hom_determining_set hN
  let T := N.subtype '' S
  have hTN : T ⊆ N := by rintro _ ⟨x, _, rfl⟩; exact x.property
  refine ⟨T, hS.image N.subtype, hTN, le_antisymm ?_ (Subgroup.centralizer_le hTN)⟩
  intro g hg
  have he : (MulAut.conjNormal (H := N) g).toMonoidHom = MonoidHom.id N := by
    apply hdet hN.torsionFree
    intro x hx
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = x
    have hcomm := Subgroup.mem_centralizer_iff.mp hg (x : G) ⟨x, hx, rfl⟩
    rw [← hcomm, mul_inv_cancel_right]
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hfix := congrArg (fun f : N →* N => ((f ⟨x, hx⟩ : N) : G)) he
  change g * x * g⁻¹ = x at hfix
  exact (mul_inv_eq_iff_eq_mul.mp hfix).symm

end PolycyclicRecognition

end

end OAI
