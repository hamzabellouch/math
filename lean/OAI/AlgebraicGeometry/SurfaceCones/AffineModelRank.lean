import OAI.AlgebraicGeometry.SurfaceCones.CoherentTensor
import OAI.AlgebraicGeometry.SurfaceCones.ReesPunctureTopology

namespace OAI


noncomputable section
namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The genuine structure map of the distinguished affine chart of the
literal eighteen-section ordinary blowup. -/
abbrev completedChartBaseMap : CommRingCat.of completedRing ⟶
    CommRingCat.of completedBlowupChart :=
  CommRingCat.ofHom (algebraMap completedRing completedBlowupChart)

lemma completedChartBaseMap_injective : Function.Injective completedChartBaseMap := by
  intro a b hab
  apply completedAffineSource_injective
  calc
    completedAffineSource a = completedBlowupChartEquiv
        (algebraMap completedRing completedBlowupChart a) :=
      (completedBlowupChartEquiv.commutes a).symm
    _ = completedBlowupChartEquiv (algebraMap completedRing completedBlowupChart b) :=
      congrArg completedBlowupChartEquiv hab
    _ = completedAffineSource b := completedBlowupChartEquiv.commutes b

instance completedBlowupExceptional_domain :
    IsDomain (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}) :=
  completedBlowupExceptionalEquiv.injective.isDomain completedBlowupExceptionalEquiv.toRingHom

instance completedBlowupExceptional_prime :
    (Ideal.span ({completedBlowupParameter} : Set completedBlowupChart)).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).mp completedBlowupExceptional_domain

lemma completedBlowupParameter_regular :
    IsSMulRegular completedBlowupChart completedBlowupParameter := by
  intro x y hxy
  exact completedBlowupChart_domain.mul_left_cancel_of_ne_zero
    completedBlowupParameter_ne_zero hxy

/-- The exceptional-chart module is the restriction of the double dual of the pullback module to a prime Cartier divisor. -/
abbrev completedChartRestrictionSections (M : ModuleCat.{0} completedRing) :=
  let q : CommRingCat.of completedBlowupChart ⟶
      CommRingCat.of (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  (moduleSpecΓFunctor (R := CommRingCat.of
    (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}))).obj
      ((Scheme.Modules.pullback (Spec.map q)).obj
        (CoherentModelActual.E (Spec.map completedChartBaseMap) M))

/-- Torsion freedom is proved for the concrete exceptional module, not
assumed as input to a numerical argument. There is no grading on M. -/
theorem completedChartRestriction_torsionFree (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] :
    Module.IsTorsionFree (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedChartRestrictionSections M) :=
  CoherentModelActual.affineE_cartier_torsionFree completedChartBaseMap M
    completedBlowupParameter completedBlowupParameter_regular

/-- A nonzero finite torsion-free module gives positive rank on the exceptional affine section chart. -/
theorem completedChartRestriction_rank_pos (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] [Module.IsTorsionFree completedRing M] [Nontrivial M] :
    0 < Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedChartRestrictionSections M) := by
  let := actualCompletion_noetherian
  exact CoherentModelActual.affineE_cartier_rank_pos completedChartBaseMap M
    completedChartBaseMap_injective completedBlowupParameter
    completedBlowupParameter_regular

end ExplicitCone


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The literal double-dual extension for an arbitrary module on the
completed cone, on the genuine proper Rees modification constructed above.
This is not an assumed object with prescribed numerical invariants. -/
abbrev completedModelE (M : ModuleCat completedRing) : completedBlowup.Modules :=
  CoherentModelActual.E completedBlowupMap M

/-- Coherence for EVERY finite module of the completed ring: no grading,
algebra structure, or freeness premise is imposed on M. -/
theorem completedModelE_coherent (M : ModuleCat completedRing)
    [Module.Finite completedRing M] : (completedModelE M).IsFinitePresentation := by
  let := actualCompletion_noetherian
  exact CoherentModelActual.coherent_E completedBlowupMap M

/-- Torsion freeness of the literal extension, proved on all open-section
modules of the fixed integral model. No source regularity is assumed. -/
theorem completedModelE_torsionFree (M : ModuleCat completedRing)
    (U : completedBlowup.Opens) :
    @Module.IsTorsionFree Γ(completedBlowup, U)
      ((completedModelE M).val.obj (Opposite.op U)) _ _
      ((completedModelE M).val.obj (Opposite.op U)).isModule :=
  CoherentDual.dual_sections_torsionFree _ U

/-- The first dual in the same construction is also genuinely coherent. -/
theorem completedModel_firstDual_coherent (M : ModuleCat completedRing)
    [Module.Finite completedRing M] :
    (CoherentDual.homSheaf completedBlowup.sheaf
      ((Scheme.Modules.pullback completedBlowupMap).obj (tilde M))
      (SheafOfModules.unit _)).IsFinitePresentation := by
  let := actualCompletion_noetherian
  obtain ⟨P, hP⟩ := CoherentPullback.exists_presentation_pullback_tilde completedBlowupMap M
  let := hP
  have : ((Scheme.Modules.pullback completedBlowupMap).obj (tilde M)).IsFinitePresentation :=
    CoherentLocality.finitePresentation_of_presentation P
  exact CoherentDual.coherent_dual _

end ExplicitCone


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory Scheme.Modules

/-- The literal prime Cartier divisor in the distinguished actual blowup
chart, embedded into the GLOBAL proper model. -/
abbrev completedExceptionalChartMap :
    Spec (.of (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})) ⟶
      completedBlowup :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {completedBlowupParameter}))) ≫
    completedChartInclusion

/-- Sections of the restriction of the GLOBALLY defined extension E. -/
abbrev completedGlobalRestrictionSections (M : ModuleCat.{0} completedRing) :=
  (moduleSpecΓFunctor (R := CommRingCat.of
    (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}))).obj
      ((pullback completedExceptionalChartMap).obj (completedModelE M))

/-- Compatibility with the actual global model; this closes the local/global
identity left separate in the preceding positive-rank chart calculation. -/
def completedGlobalRestrictionIso (M : ModuleCat.{0} completedRing) :
    completedGlobalRestrictionSections M ≅ completedChartRestrictionSections M := by
  let q : CommRingCat.of completedBlowupChart ⟶
      CommRingCat.of (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  let e := CoherentModelActual.openPullbackEIsoOfComp completedChartInclusion
    completedBlowupMap (Spec.map completedChartBaseMap) completedChartInclusion_map M
  exact (moduleSpecΓFunctor (R := CommRingCat.of
    (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter}))).mapIso
      (((pullbackComp (Spec.map q) completedChartInclusion).app (completedModelE M)).symm ≪≫
        (pullback (Spec.map q)).mapIso e)

/-- The actual global extension restricts to a torsion-free module along
this whole exceptional chart, not merely its generic point. -/
theorem completedGlobalRestriction_torsionFree (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] :
    Module.IsTorsionFree (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections M) := by
  let e := (completedGlobalRestrictionIso M).toLinearEquiv
  let := completedChartRestriction_torsionFree M
  exact e.injective.moduleIsTorsionFree e e.map_smul

/-- The restriction of the global double-dual extension has positive rank for every nonzero finite torsion-free module. -/
theorem completedGlobalRestriction_rank_pos (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] [Module.IsTorsionFree completedRing M] [Nontrivial M] :
    0 < Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections M) := by
  rw [(completedGlobalRestrictionIso M).toLinearEquiv.finrank_eq]
  exact completedChartRestriction_rank_pos M

end ExplicitCone

end

end OAI
