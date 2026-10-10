import OAI.NumberTheory.PiExponent.Approximation.SerreSectionLifting
import OAI.NumberTheory.PiExponent.Cohomology.CechH1Transfer
import OAI.NumberTheory.PiExponent.Jets.CompactJetIdealCoherent

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport

variable {X B : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def jetQuotient (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (PiExponentSeshadri.IdealModule.unit I.subscheme)

def twistedIdeal (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor A n).obj (PiExponentSeshadri.IdealModule.closedModule (I ^ n))

def jetRestriction (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient (I ^ n))) :=
  s ≫ (moduleTwistUnitIso A n).inv ≫
    (moduleTwistFunctor A n).map (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι)

theorem jetRestriction_surjective_of_h1_zero
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (hzero : ∀ x : cohomology (twistedIdeal I A n) 1, x = 0) :
    Function.Surjective (jetRestriction I A n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion (I ^ n).subschemeι)
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact (I ^ n).subschemeι
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor A n)) (moduleTwistFunctor_shortExact A n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso A n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor A n).map
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) = s at ht
  change (t ≫ (moduleTwistUnitIso A n).hom) ≫ (moduleTwistUnitIso A n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_jetRestriction_surjective_of_ample_comparison
    [IsNoetherian X]
    (f : B ⟶ X) (p : B ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (F : LineBundle B) (hF : LineBundle.IsAmple B F)
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U (fun i => f ⁻¹ᵁ U i)
        (twistedIdeal I A n) (modulePow B F.sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  obtain ⟨N₁, hN₁⟩ := NoetherianAmpleSerreVanishing.ample_power_cohomology_zero p F hF
  obtain ⟨N₂, hN₂⟩ := hcomparison
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  apply jetRestriction_surjective_of_h1_zero I A n
  let : (PiExponentSeshadri.IdealModule.closedModule (I ^ n)).IsFinitePresentation :=
    CompactJetIdeal.closedModule_isFinitePresentation (I ^ n)
  let : (twistedIdeal I A n).IsFinitePresentation :=
    FiniteGlobalPresentation.moduleTwist_isFinitePresentation A n _
  let : (twistedIdeal I A n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (twistedIdeal I A n)).choose.isQuasicoherent
  obtain ⟨P⟩ := hN₂ n ((le_max_right _ _).trans hn)
  apply P.cohomology_one_zero hU hcover _ (hN₁ n ((le_max_left _ _).trans hn) 1 (by decide))
  exact f.iSup_preimage_eq_top hcover

end
end PiExponent.BlowupJetSurjectivity

end OAI
