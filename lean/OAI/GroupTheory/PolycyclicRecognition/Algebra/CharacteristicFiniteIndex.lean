import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicFiniteGeneration

namespace OAI

/-! # Characteristic finite-index refinements

A finite-index subgroup of a finitely generated group contains a
characteristic finite-index subgroup. We intersect kernels of maps into the
finite permutation group on its cosets. This is the finite-index refinement
needed in the induction proving virtual torsion freeness.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G F : Type*} [Group G] [Group F]

theorem finite_hom_of_finitelyGenerated [Group.FG G] [Finite F] :
    Finite (G →* F) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let : Finite S := hfin
  exact Finite.of_injective (fun f : G →* F => fun s : S => f s) (by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense hS
    intro s hs
    exact congrFun h ⟨s, hs⟩)

/-- The intersection only ranges over a finite type of homomorphisms. -/
def finiteTargetKernel (G F : Type*) [Group G] [Group F] : Subgroup G :=
  ⨅ f : G →* F, f.ker

theorem finiteTargetKernel_characteristic : (finiteTargetKernel G F).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro e g hg
  change e g ∈ finiteTargetKernel G F
  simp only [finiteTargetKernel, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg ⊢
  intro f
  exact hg (f.comp e.toMonoidHom)

theorem finiteTargetKernel_finiteIndex [Group.FG G] [Finite F] :
    (finiteTargetKernel G F).FiniteIndex := by
  let : Finite (G →* F) := finite_hom_of_finitelyGenerated
  apply Subgroup.finiteIndex_iInf
  intro f
  change ((⊥ : Subgroup F).comap f).FiniteIndex
  infer_instance

theorem exists_characteristic_finiteIndex_le [Group.FG G]
    (H : Subgroup G) [H.FiniteIndex] :
    ∃ K : Subgroup G, K ≤ H ∧ K.Characteristic ∧ K.FiniteIndex := by
  let F := Equiv.Perm (G ⧸ H)
  refine ⟨finiteTargetKernel G F, ?_, finiteTargetKernel_characteristic,
    finiteTargetKernel_finiteIndex⟩
  intro g hg
  have he : MulAction.toPermHom G (G ⧸ H) g = 1 :=
    (Subgroup.mem_iInf.mp hg (MulAction.toPermHom G (G ⧸ H)))
  have hx := congrArg (fun e : Equiv.Perm (G ⧸ H) => e (QuotientGroup.mk g⁻¹)) he
  change QuotientGroup.mk (g * g⁻¹) = QuotientGroup.mk g⁻¹ at hx
  rw [mul_inv_cancel] at hx
  simpa using (QuotientGroup.eq.mp hx.symm)

end PolycyclicRecognition

end

end OAI
