import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.ProjectiveLine
import OAI.AlgebraicGeometry.RelativeTriviality.IsomorphismLocus
import OAI.AlgebraicGeometry.RelativeTriviality.CechBaseChange
import OAI.AlgebraicGeometry.RelativeTriviality.Frames

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeTriviality
open CategoryTheory AlgebraicGeometry Limits
universe u
variable (R : Type u) [CommRing R]
theorem isIso_near_isIso_fiber {F E : (line R).Modules}
    (hF : ∃ q : F.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (φ : F ⟶ E)
    [IsIso ((Scheme.Modules.pullback (fiberProjection R p)).map φ)] :
    ∃ r : R, r ∉ p.asIdeal ∧
      IsIso ((Scheme.Modules.pullback (awayProjection R r)).map φ) := by
  have h : IsIso ((Scheme.Modules.pullback (fiberProjection R p)).map φ) := inferInstance
  exact @RelativeCech.isIso_near_fiber_proper (.of R) (line R) (toBase R)
    (line_toBase_universallyClosed R) F E hF hE p φ h
end CampanaPeternellSix.RelativeTriviality

namespace CampanaPeternellSix.ActualCech
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange Scheme.Modules FiberFrame
universe u
variable {R : Type u} [CommRing R]
theorem exists_fiber_trivializing_map (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (n : ℕ)
    (hf : Nonempty ((pullback (baseMap (algebraMap R p.asIdeal.ResidueField) 1)).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin n)))) :
    ∃ φ : SheafOfModules.free (ULift.{u} (Fin n)) ⟶ E,
      IsIso ((pullback (baseMap (algebraMap R p.asIdeal.ResidueField) 1)).map φ) := by
  classical
  let S := p.asIdeal.ResidueField
  let f := baseMap (algebraMap R S) 1
  let E' := (pullback f).obj E
  let I := ULift.{u} (Fin n)
  let N := (coefficientSheaf S E').obj.obj (op ⊤)
  let : Module R N := Module.compHom N (algebraMap R S)
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e := Classical.choice hf
  let s : I → N := fun i => sectionsTopEquiv E' (E'.freeHomEquiv e.inv i)
  obtain ⟨d,hd,t,ht⟩ := RelativeCech.clear_finite_sections_denominator p.asIdeal
    (actualUnit (S := S) E ⊤ ⊤ (by intro z _; trivial))
    (global_sections_base_change_at_trivial_fiber E hE p n hf) I s
  let φ : SheafOfModules.free I ⟶ E := E.freeHomEquiv.symm
    (fun i => (sectionsTopEquiv E).symm (t i))
  have hd' : algebraMap R S d ≠ 0 := by
    change algebraMap R p.asIdeal.ResidueField d ≠ 0
    exact fun h => hd (Ideal.algebraMap_residueField_eq_zero.mp h)
  let a : Γ(RelativePolynomialEvaluation.space S 1,⊤)ˣ := Units.map (RelativeLineGlobalFunctions.scalars S).toMonoidHom
    (Units.mk0 (algebraMap R S d) hd')
  let ψ := e.inv ≫ (scalarIso E' a).hom
  have hφ : (pullbackFreeIso f).inv ≫ (pullback f).map φ = ψ := by
    apply E'.freeHomEquiv.injective
    funext i
    apply (sectionsTopEquiv E').injective
    erw [← pullbackFree_top f φ i]
    change actualUnit (S := S) E ⊤ ⊤ _
      (sectionsTopEquiv E (E.freeHomEquiv φ i)) = _
    have hti : sectionsTopEquiv E (E.freeHomEquiv φ i) = t i := by
      have h := congrFun (E.freeHomEquiv.apply_symm_apply
        (fun j : I => (sectionsTopEquiv E).symm (t j))) i
      exact (congrArg (sectionsTopEquiv E) h).trans
        ((sectionsTopEquiv E).apply_symm_apply (t i))
    rw [hti, ht]
    change algebraMap R S d • s i =
      sectionsTopEquiv E' (E'.freeHomEquiv (e.inv ≫ (scalarIso E' a).hom) i)
    erw [SheafOfModules.freeHomEquiv_comp_apply, sectionsTopEquiv_naturality]
    change algebraMap R S d • s i = (scalarEnd E' ↑a).app ⊤ (s i)
    erw [scalarEnd_app_top]
    change ((RelativePolynomialEvaluation.space S 1).presheaf.map (𝟙 (op ⊤))
      (RelativeLineGlobalFunctions.scalars S (algebraMap R S d))) •
        (show Γ(E',⊤) from s i) =
      (RelativeLineGlobalFunctions.scalars S (algebraMap R S d)) •
        (show Γ(E',⊤) from s i)
    simp

  refine ⟨φ, ?_⟩
  have : IsIso ψ := IsIso.comp_isIso' e.isIso_inv (scalarIso E' a).isIso_hom
  have : IsIso ((pullbackFreeIso f).inv ≫ (pullback f).map φ) := by rw [hφ]; infer_instance
  let : IsIso (pullbackFreeIso f (I := I)).inv := (pullbackFreeIso f (I := I)).isIso_inv
  exact IsIso.of_isIso_comp_left (pullbackFreeIso f (I := I)).inv ((pullback f).map φ)
end CampanaPeternellSix.ActualCech

namespace CampanaPeternellSix.RelativeTriviality
open CategoryTheory AlgebraicGeometry Limits
open Scheme.Modules
universe u
variable (R : Type u) [CommRing R]
theorem trivial_near_trivial_fiber (E : (line R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (n : ℕ)
    (hf : Nonempty ((Scheme.Modules.pullback (fiberProjection R p)).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin n)))) :
    ∃ r : R, r ∉ p.asIdeal ∧ Nonempty
      ((Scheme.Modules.pullback (awayProjection R r)).obj E ≅
        SheafOfModules.free (ULift.{u} (Fin n))) := by
  classical
  let S := p.asIdeal.ResidueField
  let g := RelativeProjectiveBaseChange.baseMap (algebraMap R S) 1
  have hc : IsPullback g (RelativePolynomialEvaluation.toBase S 1) (toBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    RelativeProjectiveBaseChange.baseMap_isPullback _
  let e := hc.isoPullback
  have heg : e.hom ≫ fiberProjection R p = g := hc.isoPullback_hom_fst
  have hge : e.inv ≫ g = fiberProjection R p := hc.isoPullback_inv_fst
  have hfg : Nonempty ((Scheme.Modules.pullback g).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin n))) := by
    refine ⟨(pullbackCongr heg.symm).app E ≪≫
      (pullbackComp e.hom (fiberProjection R p)).symm.app E ≪≫
      (Scheme.Modules.pullback e.hom).mapIso (Classical.choice hf) ≪≫
      FiberFrame.pullbackFreeIso e.hom⟩
  obtain ⟨φ, hφ⟩ := ActualCech.exists_fiber_trivializing_map E hE p n hfg
  have : IsIso ((Scheme.Modules.pullback g).map φ) := hφ
  have hpb : IsIso ((Scheme.Modules.pullback e.inv).map
      ((Scheme.Modules.pullback g).map φ)) := Functor.map_isIso _ _
  have : IsIso ((Scheme.Modules.pullback (e.inv ≫ g)).map φ) :=
    (NatIso.isIso_map_iff (pullbackComp e.inv g) φ).mp hpb
  have hfφ : IsIso ((Scheme.Modules.pullback (fiberProjection R p)).map φ) :=
    (NatIso.isIso_map_iff (pullbackCongr hge) φ).mp inferInstance
  let I := ULift.{u} (Fin n)
  let F : (line R).Modules := SheafOfModules.free I
  let q := (SheafOfModules.free.generatingSections (R := (line R).ringCatSheaf) I).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have ht : q.IsFiniteType := by
    constructor
    intro U
    constructor
    change Finite I
    infer_instance
  obtain ⟨r,hr,hiso⟩ := @isIso_near_isIso_fiber R _ F E ⟨q,hq,ht⟩ hE p φ hfφ
  refine ⟨r,hr,⟨(@asIso _ _ _ _ ((Scheme.Modules.pullback (awayProjection R r)).map φ) hiso).symm ≪≫
    FiberFrame.pullbackFreeIso (awayProjection R r)⟩⟩
end CampanaPeternellSix.RelativeTriviality

end

end OAI
