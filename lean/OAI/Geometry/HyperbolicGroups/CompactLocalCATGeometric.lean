import Mathlib
import OAI.Geometry.HyperbolicGroups.DevelopmentGeometricAction
import OAI.Geometry.HyperbolicGroups.LocalGeodesic
import OAI.Geometry.HyperbolicGroups.GeometricSpaceTransport

namespace OAI

section


/-! Compact locally CAT(-1) geodesic metrics yield genuine geometric CAT(0)
actions of the actual fundamental group. -/
noncomputable section
namespace HyperbolicObstruction
open Set Metric
open scoped Topology ContinuousMap
universe u

lemma not_noGeometricCATZeroAction_of_compact_localCATNegOne
    {X : Type} [MetricSpace X] [CompactSpace X] (o : X) (g : IsGeodesic X)
    (hl : ∀ x : X, ∃ r : ℝ, 0<r ∧ CATNegOne (ball x r)) :
    ¬ NoGeometricCATZeroAction.{u} (FundamentalGroup X o) := by
  intro h
  obtain ⟨r,hr,hc⟩:=uniformLocalCATZero_of_compact hl
  let e := LocalGeodesic.deckPiOneEquiv (o:=o) hr hc g
  let A := LocalGeodesic.deckGeometricAction (o:=o) hr hc g
  let := LocalGeodesic.intrinsicMetric (o:=o) hr hc g
  let := LocalGeodesic.developed_proper (o:=o) hr hc g
  let : Nonempty (LocalGeodesic o) := ⟨LocalGeodesic.constant o⟩
  let Y := ULift.{u} (LocalGeodesic o)
  let : ProperSpace Y := ulift_proper
  have hcat : CATZero Y := CATZero.of_isometryEquiv (uliftIsometry (LocalGeodesic o))
    (LocalGeodesic.developed_catZero hr hc g)
  have : IsEmpty (GeometricAction (FundamentalGroup X o) Y) :=
    h Y inferInstance inferInstance inferInstance inferInstance hcat
  exact isEmptyElim ((A.pullback e).spaceTransport (uliftIsometry (LocalGeodesic o)))

lemma incompatibleLocalCATNegOne_of_noAction (L : FiniteComplex) (y : L.Carrier)
    (h : NoGeometricCATZeroAction.{u} (FundamentalGroup L.Carrier y)) :
    ¬ CompatibleLocallyCATNegOne L := by
  rintro ⟨m,hm,hg,hl⟩
  have hcompact : CompactSpace L.Carrier :=
    inferInstanceAs (CompactSpace (FinitePolyhedron.Carrier L.complex))
  let P : TopologicalSpace L.Carrier → Prop := fun t =>
    letI := t
    NoGeometricCATZeroAction.{u} (FundamentalGroup L.Carrier y)
  let := m
  let : TopologicalSpace L.Carrier := m.toUniformSpace.toTopologicalSpace
  let : CompactSpace L.Carrier := by
    change @CompactSpace L.Carrier m.toUniformSpace.toTopologicalSpace
    rw [hm]
    exact hcompact
  apply not_noGeometricCATZeroAction_of_compact_localCATNegOne y hg hl
  exact (congrArg P hm).mpr h

lemma homotopy_incompatibleLocalCATNegOne {K L : FiniteComplex} (x : K.Carrier)
    (h : NoGeometricCATZeroAction.{u} (FundamentalGroup K.Carrier x))
    (e : K.Carrier ≃ₕ L.Carrier) : ¬ CompatibleLocallyCATNegOne L :=
  incompatibleLocalCATNegOne_of_noAction L (e x)
    (h.of_mulEquiv (fundamentalGroupHomotopyEquiv e x))

end HyperbolicObstruction
end
end

section

end

end OAI
