import OAI.Analysis.CircleDomains.Rigidity.ExactTraceFamily
import OAI.Analysis.CircleDomains.Modulus.NormalizedUniformization

namespace OAI

/-! Source data and a common exterior zero anchor for a finite family of
compact tests on a point-complement sphere domain. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

def pointDustPathData (G A : Set Sphere) : PathCodeData Sphere Sphere where
  physicalDomain := G
  quotientDomain := G
  domainEquiv := Homeomorph.refl G
  basePoint := OnePoint.infty
  dust := Gᶜ
  levels := fun _ => ∅
  priorLaws := fun _ => 0
  priorDeletions := fun _ _ => ∅
  flagDeletions := fun _ => ∅
  levelWeights := fun _ _ => 0
  anchor := A
  target := OnePoint.infty
  gateContours := fun _ => ∅
  gateSets := fun _ => ∅

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem point_component_eq_of_totallyDisconnected
    {G : Set Sphere} (hTD : IsTotallyDisconnected Gᶜ)
    (q p : Sphere) (hp : p ∈ connectedComponentIn Gᶜ q) : p = q := by
  have hq : q ∈ Gᶜ := connectedComponentIn_nonempty_iff.mp ⟨p, hp⟩
  exact hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn
    hp (mem_connectedComponentIn hq)

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem plane_complement_nonempty {G : Set Sphere}
    (hinf : OnePoint.infty ∈ G) (hne : Gᶜ.Nonempty) :
    (physicalPlaneDomain G)ᶜ.Nonempty := by
  obtain ⟨p, hp⟩ := hne
  have hpn : p ≠ OnePoint.infty := fun h => hp (h ▸ hinf)
  obtain ⟨x, rfl⟩ := exists_planeSphere_eq hpn
  exact ⟨x, hp⟩

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem exists_common_test_anchor
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {m : ℕ} (v : Fin m → EuclideanPlane → ℝ) (hs : ∀ i, HasCompactSupport (v i)) :
    ∃ E A : Set Sphere, IsCompact E ∧ IsClosed A ∧ E ⊆ interior A ∧ A ⊆ G ∧
      OnePoint.infty ∈ interior E ∧ ∀ i p, p ∈ E → sphereFromPlaneFunction (v i) p = 0 := by
  let K : Set Sphere := ⋃ i, planeSphere '' tsupport (v i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hs i).isCompact.image continuous_planeSphere)
  have hinK : OnePoint.infty ∉ K := by
    intro hp
    obtain ⟨i, x, _, hx⟩ := mem_iUnion.mp hp
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hx
  have hZ : IsOpen (G \ K) := hG.sdiff hK.isClosed
  obtain ⟨E, hE, _, hinE, hEZ⟩ := exists_compact_closed_between
    (isCompact_singleton (x := (OnePoint.infty : Sphere))) hZ
    (singleton_subset_iff.mpr ⟨hinf, hinK⟩)
  obtain ⟨A, _, hA, hEA, hAG⟩ := exists_compact_closed_between hE hG (hEZ.trans sdiff_subset)
  refine ⟨E, A, hE, hA, hEA, hAG, hinE (mem_singleton _), ?_⟩
  intro i p hp
  have hpK := (hEZ hp).2
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hpK (mem_iUnion.mpr ⟨i, complexPlaneCoordinates.symm z, hz, by
      simp only [planeSphere, ContinuousLinearEquiv.apply_symm_apply]⟩)

end CircleDomainRigidity

end

end OAI
