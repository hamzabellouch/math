import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
import OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple
import OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveInequality
import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def scale : Scale d.curveDegreeWeights d.curveJetWeights :=
  chooseScale d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos

abbrev Index := (scale d).Index
abbrev exponents : Index d → Fin (d.m+1) →₀ ℕ := (scale d).exponents
abbrev constantIndex : Index d := (scale d).constantIndex d.curveDegreeWeights_pos
abbrev coordinateIndex : Fin (d.m+1) → Index d :=
  (scale d).coordinateIndex d.curveDegreeWeights_pos
abbrev pureIndex : Fin (d.m+1) → Index d :=
  (scale d).pureIndex d.curveDegreeWeights_pos

instance index_nonempty : Nonempty (Index d) := ⟨constantIndex d⟩

abbrev compactification : Scheme := Proj (WeightedCompactification.imageGrade (R := ℂ) (exponents d))

def compactificationStructureMap : compactification d ⟶ Spec (.of ℂ) :=
  WeightedCompactification.projection (exponents d)

instance compactificationStructureMap_proper : IsProper (compactificationStructureMap d) := by
  dsimp [compactificationStructureMap]
  infer_instance

def affineChart : CompactLogJetIdeal.affineSpace d.m ⟶ compactification d :=
  WeightedCompactification.affineChartMap (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart d) := by
  dsimp [affineChart]
  infer_instance

def origin : CompactLogJetIdeal.affineSpace d.m :=
  ⟨WeightedBezout.pointIdeal (0 : Fin (d.m+1) → ℂ),inferInstance⟩

instance compactification_nonempty : Nonempty (compactification d) := ⟨affineChart d (origin d)⟩
instance compactification_isIntegral : IsIntegral (compactification d) := by infer_instance
instance compactification_isLocallyNoetherian : IsLocallyNoetherian (compactification d) :=
  LocallyOfFiniteType.isLocallyNoetherian (compactificationStructureMap d)
instance compactification_compact : CompactSpace (compactification d) :=
  QuasiCompact.compactSpace_of_compactSpace (compactificationStructureMap d)
instance compactification_isNoetherian : IsNoetherian (compactification d) := {}
instance affineChart_quasiCompact : QuasiCompact (affineChart d) := by infer_instance

theorem affineChart_over : affineChart d ≫ compactificationStructureMap d =
    CompactLogJetIdeal.structureMap d.m :=
  CurveMonomialMap.affineChartMap_projection (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

def hyperplane : LineBundle (compactification d) := WeightedCompactification.lineBundle (exponents d)
theorem hyperplane_ample : (hyperplane d).IsAmple :=
  WeightedCompactification.lineBundle_ample (exponents d)

def logCutoff : Fin d.m → ℕ :=
  (exists_log_cutoff d.curveJetWeights (d.curveJetWeights_pos 0)).choose

theorem logCutoff_strict (i : Fin d.m) :
    d.curveJetWeights i.succ < (logCutoff d i : ℚ) * d.curveJetWeights 0 :=
  (exists_log_cutoff d.curveJetWeights (d.curveJetWeights_pos 0)).choose_spec i

def centerIdeal : (compactification d).IdealSheafData :=
  CompactLogJetIdeal.compactIdeal d.curveCenters (logCutoff d) (scale d).jetPowers (affineChart d)

theorem centerIdeal_restrict : (centerIdeal d).comap (affineChart d) =
    CompactLogJetIdeal.affineIdeal d.curveCenters (logCutoff d) (scale d).jetPowers :=
  CompactLogJetIdeal.restrict_compactIdeal _ _ _ _

theorem centerIdeal_support : ((centerIdeal d).support : Set (compactification d)) =
    ⋃ j : Fin d.K, Set.range (CompactLogJetIdeal.point (d.curveCenters j) ≫ affineChart d) :=
  CompactLogJetIdeal.support_compactIdeal _ _ _ (scale d).jetPowers_pos _
    (compactificationStructureMap d) (affineChart_over d)

theorem centerIdeal_support_finite :
    ((centerIdeal d).support : Set (compactification d)).Finite := by
  rw [centerIdeal_support]
  exact Set.finite_iUnion (fun _ => Set.finite_range _)

theorem centerIdeal_support_subset_chart :
    ((centerIdeal d).support : Set (compactification d)) ⊆ (affineChart d).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactLogJetIdeal.point (d.curveCenters j) z,rfl⟩

theorem centerIdeal_coherent :
    (PiExponentSeshadri.IdealModule.closedModule (centerIdeal d)).IsFinitePresentation :=
  CompactLogJetIdeal.compactIdeal_isFinitePresentation _ _ _ _

theorem origin_ne_center (c : Fin d.m → ℂ) : origin d ≠ CompactJetPolynomial.centerPoint c := by
  intro h
  have hx : MvPolynomial.X (0 : Fin (d.m+1)) ∈ (origin d).asIdeal := by
    change MvPolynomial.aeval (0 : Fin (d.m+1) → ℂ) (MvPolynomial.X 0) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (CompactJetPolynomial.center c) (MvPolynomial.X 0) = 0 at hx
  simp [CompactJetPolynomial.center] at hx

theorem origin_avoids_center : affineChart d (origin d) ∉ (centerIdeal d).support := by
  change affineChart d (origin d) ∉ ((centerIdeal d).support : Set (compactification d))
  rw [centerIdeal_support]
  intro h
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨z,hz⟩ := hj
  have he : CompactLogJetIdeal.point (d.curveCenters j) z = origin d :=
    (affineChart d).isOpenEmbedding.injective hz
  have hc : CompactLogJetIdeal.point (d.curveCenters j) z =
      CompactJetPolynomial.centerPoint (d.curveCenters j) := by
    apply Set.mem_singleton_iff.mp
    erw [← CompactLogJetIdeal.range_point]
    exact ⟨z,rfl⟩
  exact origin_ne_center d _ (he.symm.trans hc)

theorem centerIdeal_support_ne_top : (centerIdeal d).support ≠ ⊤ := by
  intro h
  exact origin_avoids_center d (by rw [h]; trivial)

abbrev blowup : Scheme := PiExponentSeshadri.BlowupGluing.scheme (centerIdeal d)
abbrev projection : blowup d ⟶ compactification d :=
  PiExponentSeshadri.BlowupGluing.projection (centerIdeal d)
def structureMap : blowup d ⟶ Spec (.of ℂ) := projection d ≫ compactificationStructureMap d

instance projection_proper : IsProper (projection d) := by infer_instance
instance structureMap_proper : IsProper (structureMap d) := by
  dsimp [structureMap]
  infer_instance
instance blowup_isIntegral : IsIntegral (blowup d) :=
  PiExponentSeshadri.BlowupGluing.scheme_isIntegral (centerIdeal d) (centerIdeal_support_ne_top d)
instance blowup_isLocallyNoetherian : IsLocallyNoetherian (blowup d) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap d)
instance blowup_compact : CompactSpace (blowup d) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap d)
instance blowup_isNoetherian : IsNoetherian (blowup d) := {}

def A : LineBundle (blowup d) := (hyperplane d).pullback (projection d)
abbrev J : LineBundle (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalLineBundle (centerIdeal d)
abbrev exceptionalInclusion : (J d).sheaf ⟶ structureSheaf (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalInclusion (centerIdeal d)

theorem exceptional_presents :
    PresentsPullbackIdeal (centerIdeal d) (projection d) (J d) (exceptionalInclusion d) :=
  PiExponentSeshadri.BlowupGluing.exceptional_presents (centerIdeal d)

theorem isBlowup : IsBlowup (centerIdeal d) (projection d) :=
  PiExponentSeshadri.BlowupGluing.isBlowup (centerIdeal d)

abbrev affinePolynomialIdeal :=
  CompactLogJetIdeal.polynomialIdeal d.curveCenters (logCutoff d) (scale d).jetPowers

theorem formalJet_packet_zero (n : ℕ) (P : CompactLogJetIdeal.coordinateRing d.m)
    (hP : P ∈ affinePolynomialIdeal d ^ n) (j : Fin d.K) :
    JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
      (FormalLogJet.formalJet (d.curveCenters j) P) = (fun _ => (0 : ℂ)) := by
  apply CompactLogJetIdeal.formalJet_packet_zero_of_mem_polynomialIdeal_pow
    d.curveCenters (logCutoff d) (scale d).jetPowers d.curveJetWeights
    (fun i => (d.curveJetWeights_pos i).le) (fun i => (logCutoff_strict d i).le)
    (scale d).radius (fun i => ?_) n P hP j
  rw [mul_comm, (scale d).jetPowers_eq]

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
