import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Modulus.NormalizedComponentShrinking
import OAI.Analysis.CircleDomains.Uniformization.SelectedUniformization
import OAI.Analysis.CircleDomains.Selection.SelectedMixedSelection
import OAI.Analysis.CircleDomains.Selection.PresentedRealSeed
import OAI.Analysis.CircleDomains.Uniformization.Conformal
import OAI.Analysis.CircleDomains.Selection.DenseComplementaryDust
import OAI.Analysis.CircleDomains.Topology.AnchoredCollarFamily
import OAI.Analysis.CircleDomains.Selection.ExteriorZeroAnchor
import OAI.Analysis.CircleDomains.Sobolev.SphereChartDerivativeDecay
import OAI.Analysis.CircleDomains.Modulus.PositiveCountableWeights

namespace OAI

/-! Assemble the actual graded real seed, countable open exclusion selection,
common mixed models and their normal limit into a circle uniformization. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem circle_uniformization_of_infty_mem_of_shrinking
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
    (hinf : OnePoint.infty ∈ G) (hproper : G ≠ univ) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere), IsCircleDomain V ∧ IsConformalEquivalence f G V := by
  classical
  obtain ⟨π, hπ, hclosed, hsurj, hr, hfix, hinftyU, hU, ⟨e, he⟩, hTD⟩ :=
    normalized_component_quotient_of_shrinking hsard hsch hG hconn hinf
  let U := π '' G
  have hdense : Dense U := by
    simpa only [compl_compl] using dense_compl_of_totallyDisconnected_sphere hTD
  have hbad : ∀ x ∈ Gᶜ, π x ∈ Uᶜ := by
    intro x hx
    rintro ⟨y, hy, hxy⟩
    rcases (hr y x).mp hxy with h | ⟨hy', _⟩
    · exact hx (h ▸ hy)
    · exact hy' hy
  have hBimage : Uᶜ = π '' Gᶜ := by
    apply Subset.antisymm
    · intro p hp
      obtain ⟨x, rfl⟩ := hsurj p
      exact ⟨x, (fun hx => hp ⟨x, hx, rfl⟩), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hbad x hx
  have hBne : (Uᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem G).mp hproper
    exact ⟨π x, hbad x hx⟩
  obtain ⟨EStar, hEStar, _, hinStar, hStarU⟩ :=
    exists_compact_closed_between (isCompact_singleton (x := π OnePoint.infty)) hU
      (singleton_subset_iff.mpr (hfix.symm ▸ hinftyU))
  obtain ⟨Anchor, _, hAnchor, hStarAnchor, hAnchorU⟩ :=
    exists_compact_closed_between hEStar hU hStarU
  let d : PathCodeData Sphere Sphere := {
    physicalDomain := G
    quotientDomain := U
    domainEquiv := e
    basePoint := OnePoint.infty
    dust := Uᶜ
    levels := fun _ => ∅
    priorLaws := fun _ => 0
    priorDeletions := fun _ _ => ∅
    flagDeletions := fun _ => ∅
    levelWeights := fun _ _ => 0
    anchor := Anchor
    target := OnePoint.infty
    gateContours := fun _ => ∅
    gateSets := fun _ => ∅ }
  have hpiinf : π OnePoint.infty ∉ d.dust := by
    change ¬ π OnePoint.infty ∈ Uᶜ
    exact fun h => h (hfix.symm ▸ hinftyU)
  obtain ⟨D, hnest, hshrink, hED⟩ := exists_anchored_collar_family hcoarea hsard hsch
    G π hπ hclosed hsurj hr Uᶜ hU.isClosed_compl hTD hbad hpiinf Anchor hAnchor
    (disjoint_compl_right.mono_left hAnchorU)
  have hinStar' : π OnePoint.infty ∈ interior EStar := hinStar (mem_singleton _)
  obtain ⟨B, _, hfar⟩ := exists_exterior_in_quotient_neighborhood hπ hinStar'
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  obtain ⟨ω, hω, hωsum⟩ := exists_positive_summable_weights TupleType
  have hωsum' : (∑' i, ω i) < ∞ := lt_of_le_of_lt hωsum (by simp)
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum'
  exact exists_selected_circle_uniformization hcross hplane hcoarea hLusin hsard hsch
    hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero d hU hconn hG
    disjoint_compl_right π hπ hclosed hsurj hr he rfl hBne hinftyU hU.isClosed_compl hTD
    (by simp [d]) hdense hpiinf hbad hinf EStar hAnchor hAnchorU hEStar hStarAnchor
    (hStarAnchor (interior_subset hinStar')) hinStar' B hfar hBimage D hnest hshrink hED
    (connected_fibers_of_component_collapse G π hsurj hr) harcs C hC hderiv hstandard hpath
    ω (fun i => (hω i).ne') hωsum' hdual hlift


theorem circle_uniformization_of_infty_mem
    (_hmoore : MooreSphereDecomposition)
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
    (hinf : OnePoint.infty ∈ G) (hproper : G ≠ univ) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere), IsCircleDomain V ∧ IsConformalEquivalence f G V := by
  exact circle_uniformization_of_infty_mem_of_shrinking hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hconn hinf hproper

end CircleDomainRigidity

end

end OAI
