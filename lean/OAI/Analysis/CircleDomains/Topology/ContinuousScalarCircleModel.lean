import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModel
import OAI.Analysis.CircleDomains.Topology.ScalarCircleModel

namespace OAI

/-! The finite-list model construction for continuous compact planar
tests on a point-complement domain from retained tests. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_compact_scalar_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) (hBne : Gᶜ.Nonempty)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hunit : ∀ i x, u i x ∈ Icc 0 1)
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    Nonempty (CompactScalarCircleModel G u) := by
  classical
  let d₀ := pointDustPathData G ∅
  obtain ⟨T₀, _⟩ := exists_exact_trace_family d₀ hG (fun x => rfl)
    (plane_complement_nonempty hinf hBne) u hu hs hunit H (ε := 1) (by norm_num)
  obtain ⟨E, A, hE, hA, hEA, hAG, hinE, hzeroAnchor⟩ :=
    exists_common_test_anchor hG hinf (fun i => (T₀ i).smooth) (fun i => (T₀ i).compact)
  let d := pointDustPathData G A
  choose Q hQ hQc hnorm using fun i =>
    exists_prescribed_plane_coordinate d hG (fun x => rfl) (T₀ i).smooth
      (T₀ i).continuous (T₀ i).compact (T₀ i).contDiff (T₀ i).unit (T₀ i).partial_memLp
  let T : ∀ i, ExactTraceTest d (u i) := fun i => {
    smooth := (T₀ i).smooth
    continuous := (T₀ i).continuous
    compact := (T₀ i).compact
    contDiff := (T₀ i).contDiff
    unit := (T₀ i).unit
    partial_memLp := (T₀ i).partial_memLp
    trace := (T₀ i).trace
    coordinate := Q i
    coordinate_eq := hQ i
    coordinate_continuous := hQc i
    error := (T₀ i).error }
  have hcc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → p = q :=
    point_component_eq_of_totallyDisconnected hTD
  have hr : ∀ x y : Sphere, id x = id y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x) := by
    intro x y
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact (hcc x y h.2).symm
  have hdense : Dense G := by
    simpa only [compl_compl] using dense_compl_of_totallyDisconnected_sphere hTD
  have hbad : ∀ x ∈ Gᶜ, id x ∈ Gᶜ := fun _ hx => hx
  obtain ⟨D, hnest, hshrink, hED⟩ := exists_anchored_collar_family hcoarea hsard hsch
    G id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id hr Gᶜ hG.isClosed_compl hTD hbad
    (show id OnePoint.infty ∉ Gᶜ from not_not.mpr hinf) A hA
    (disjoint_compl_right.mono_left hAG)
  obtain ⟨B, _, hfar⟩ := exists_exterior_in_quotient_neighborhood continuous_id hinE
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  obtain ⟨ω, hω, hωsum⟩ := exists_positive_summable_weights TupleType
  have hωsum' : (∑' i, ω i) < ∞ := lt_of_le_of_lt hωsum (by simp)
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum'
  obtain ⟨R⟩ := exists_retained_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch
    hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    d hG hconn hG disjoint_compl_right id continuous_id (Homeomorph.refl Sphere).isClosedMap surjective_id hr
    (fun x => rfl) rfl hBne hinf hG.isClosed_compl hTD (by simp [d, pointDustPathData]) hdense
    (show id OnePoint.infty ∉ d.dust from not_not.mpr hinf) hbad hinf
    E hA hAG hE hEA (hEA (interior_subset hinE)) hinE B hfar (by simp [d, pointDustPathData]) D
    hnest hshrink hED (fun x => by simpa only [preimage_id] using isConnected_singleton (x := x))
    harcs C hC hderiv hstandard hpath ω (fun i => (hω i).ne') hωsum' hdual hlift
    (fun i => (T i).coordinate) (fun i => (T i).coordinate_continuous)
    (fun i p hp => by rw [(T i).coordinate_eq]; exact hzeroAnchor i p hp)
    (exactTraceFamily_pair_null T (Subset.refl _) hpair)
  exact ⟨R.compactScalarCircleModel harea hsch hG hcc T hu hs⟩

end CircleDomainRigidity

end

end OAI
