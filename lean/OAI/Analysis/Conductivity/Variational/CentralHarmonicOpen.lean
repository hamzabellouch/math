import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralEuclideanBridge
import OAI.Analysis.Conductivity.Branching.ChildInverse
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalRegion

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def centralStrict : Set Coord3 := {y | centralThickness<sourceCollarTime y ∧
  ∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness}

lemma centralStrict_open : IsOpen centralStrict := by
  have he : {y : Coord3 | ∀ k : Fin 2,
      sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness} =
      ⋂ k : Fin 2,{y : Coord3 | sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness} := by
    ext y
    simp only [mem_iInter,mem_ofPred_eq]
  change IsOpen ({y : Coord3 | centralThickness<sourceCollarTime y} ∩
    {y : Coord3 | ∀ k : Fin 2,sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)< -centralThickness})
  rw [he]
  apply IsOpen.inter (isOpen_lt continuous_const locallyLipschitz_sourceCollarTime.continuous)
  exact isOpen_iInter_of_finite (fun k : Fin 2 => isOpen_lt
    (locallyLipschitz_sourceCollarTime.continuous.comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous) continuous_const)

lemma centralStrict_subset : centralStrict⊆centralPhysical := fun y hy =>
  (centralPhysical_time_iff y).mpr ⟨hy.1.le,fun k => (hy.2 k).le⟩

lemma centralStrict_conull : ∀ᵐ y : Coord3,y∈centralPhysical → y∈centralStrict := by
  have hp := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hc (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hp,ae_all_iff.mpr hc] with y hp hc hy
  have ht := (centralPhysical_time_iff y).mp hy
  exact ⟨lt_of_le_of_ne ht.1 hp.symm,fun k => lt_of_le_of_ne (ht.2 k) (hc k)⟩

lemma centralStrict_harmonic : (WithLp.ofLp : R3 → Coord3) ⁻¹' centralStrict⊆centralHarmonicRegion := by
  intro x hx
  refine ⟨centralStrict_subset hx,?_⟩
  intro i θ he
  have hpair : sourcePairCoordinates (WithLp.ofLp x)=centralBoundary i θ := he
  have hinj : Function.Injective sourcePairCoordinates := sourcePairCLE.injective
  fin_cases i
  · have he' : WithLp.ofLp x=sourceAngularCollar centralThickness θ := hinj hpair
    have ht := hx.1
    rw [he',sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht
  · have he' : WithLp.ofLp x=sourceChildCoordinates 1 (sourceAngularCollar (-centralThickness) θ) := hinj hpair
    have ht := hx.2 0
    change sourceCollarTime ((sourceChildHomeomorph 1).symm (WithLp.ofLp x))< -centralThickness at ht
    rw [he',show sourceChildCoordinates 1=(sourceChildHomeomorph 1) from rfl,
      (sourceChildHomeomorph 1).symm_apply_apply,sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht
  · have he' : WithLp.ofLp x=sourceChildCoordinates (-1) (sourceAngularCollar (-centralThickness) θ) := hinj hpair
    have ht := hx.2 1
    change sourceCollarTime ((sourceChildHomeomorph (-1)).symm (WithLp.ofLp x))< -centralThickness at ht
    rw [he',show sourceChildCoordinates (-1)=(sourceChildHomeomorph (-1)) from rfl,
      (sourceChildHomeomorph (-1)).symm_apply_apply,sourceAngular_time (by norm_num [centralThickness])] at ht
    exact lt_irrefl _ ht

end ScalarConductivity

end
end

end OAI
