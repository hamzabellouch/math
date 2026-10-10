import OAI.GroupTheory.PolycyclicRecognition.Algebra.CofiberConnecting

namespace OAI

/-! # Cohomology of a cone whose induced map is injective -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable {k G : Type} [CommRing k] [Group G]
  {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G)

theorem cofiberCochain_connecting_mono (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    Mono ((cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y hxy
  apply (ModuleCat.mono_iff_injective
    (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)).mp inferInstance
  have h := cofiberCochain_connecting φ A i
  have hx := congrArg (fun f => f.hom x) h
  have hy := congrArg (fun f => f.hom y) h
  exact hx.symm.trans ((congrArg
    (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i).hom.hom hxy).trans hy)

theorem cofiberCochain_homologyProjection_zero (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    HomologicalComplex.homologyMap (cofiberCochainProjection φ A) i = 0 := by
  let := cofiberCochain_connecting_mono φ A i
  have h := (cofiberCochainSequence_shortExact φ A).comp_δ i (i + 1) rfl
  change HomologicalComplex.homologyMap (cofiberCochainProjection φ A) i ≫
    (cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl = 0 at h
  exact (cancel_mono ((cofiberCochainSequence_shortExact φ A).δ i (i + 1) rfl)).mp
    (h.trans (zero_comp).symm)

theorem cofiberCochain_homologyInclusion_epi (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)] :
    Epi (HomologicalComplex.homologyMap (cofiberCochainInclusion φ A) i) :=
  ((cofiberCochainSequence_shortExact φ A).homology_exact₂ i).epi_f
    (cofiberCochain_homologyProjection_zero φ A i)

def cofiberCochainCokernelIso (i : ℕ)
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) (i + 1))] :
    cokernel (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i) ≅
      (ChainComplex.linearYonedaObj (repCofiber φ) k A).homology (i + 1) := by
  let S := cofiberCochainSequence φ A
  let hS := cofiberCochainSequence_shortExact φ A
  let : Epi (HomologicalComplex.homologyMap (cofiberCochainSequence φ A).f (i + 1)) :=
    cofiberCochain_homologyInclusion_epi φ A (i + 1)
  let e := cokernel.mapIso (hS.δ i (i + 1) rfl)
    (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) i)
    (Iso.refl _) (cochainSuccessorHomologyIso (P.linearYonedaObj k A) i)
    ((cofiberCochain_connecting φ A i).trans (Category.id_comp _).symm)
  exact e.symm ≪≫ (cokernelIsCokernel _).coconePointUniqueUpToIso
    (hS.homology_exact₁ i (i + 1) rfl).gIsCokernel

theorem cofiberCochain_homology_zero
    [Mono (HomologicalComplex.homologyMap (repCochainPrecomp k φ A) 0)] :
    IsZero ((ChainComplex.linearYonedaObj (repCofiber φ) k A).homology 0) := by
  let := cofiberCochain_homologyInclusion_epi φ A 0
  let := ModuleCat.subsingleton_of_isZero
    (cochainSuccessor_homology_zero (P.linearYonedaObj k A))
  apply ModuleCat.isZero_of_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq (0 : (ChainComplex.linearYonedaObj (repCofiber φ) k A).homology 0)
  intro y
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (cofiberCochainInclusion φ A) 0)).mp inferInstance y
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx, map_zero]

end PolycyclicRecognition

end

end OAI
