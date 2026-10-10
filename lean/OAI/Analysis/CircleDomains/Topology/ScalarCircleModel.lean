import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.RetainedCircleModel
import OAI.Analysis.CircleDomains.Selection.PrescribedScalarSeed

namespace OAI

/-! The null trace-pair hypothesis gives a circle-domain model retaining
exactly the prescribed continuous smooth scalar tests. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 def RetainedRealCircleModel.select
    {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m k : ℕ}
    {Q : Fin m → PhysicalRealCoordinate d π} (M : RetainedRealCircleModel d π Q)
    (f : Fin k → Fin m) : RetainedRealCircleModel d π (Q ∘ f) where
  marks := M.marks
  marks_countable := M.marks_countable
  coordinates := M.coordinates
  source := M.source
  model := M.model
  limit := M.limit
  circle := M.circle
  index := M.index ∘ f
  physical := fun i => M.physical (f i)
  quotient := fun i => M.quotient (f i)

theorem exists_retained_scalar_circle_model
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hconn : IsConnected d.physicalDomain) (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hdust : d.dust = d.quotientDomainᶜ) (hne : d.dust.Nonempty)
    (hinftyU : OnePoint.infty ∈ d.quotientDomain)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (hinfStar : π OnePoint.infty ∈ interior EStar)
    (B : ℝ) (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ EStar)
    (hBimage : d.dust = π '' d.physicalDomainᶜ)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : d.dust, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : d.dust, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)] (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
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
    {m : ℕ} (Q : Fin m → PhysicalRealCoordinate d π)
    (hQ : ∀ i, Continuous (Q i).quotient)
    (hz : ∀ i x, x ∈ EStar → (Q i).quotient x = 0)
    (hpair : ∀ i j, i ≠ j → volume
      ((fun x => ((Q i).quotient x, (Q j).quotient x)) '' d.dust) = 0) :
    Nonempty (RetainedRealCircleModel d π Q) := by
  let W (i : Fin m) := (Q i).continuousTest (hQ i) (hz i) hdense
  let c := finiteScalarSeedTests W
  let T (i : Fin (m + 1)) := c i.val
  have hc (n : ℕ) : Continuous (c n).coordinate.quotient := by
    cases n with
    | zero => exact continuous_const
    | succ n =>
      by_cases hn : n < m
      · simpa only [c, finiteScalarSeedTests, dite_eq_left hn, W,
          PhysicalRealCoordinate.continuousTest] using hQ ⟨n, hn⟩
      · simp only [c, finiteScalarSeedTests, dite_eq_right hn,
          UngatedRealTest.zeroTest, PhysicalRealCoordinate.zero]
        exact continuous_const
  have hpairs := finiteScalarSeedTests_pair_null W hpair
  have hT (j : Fin (m + 1)) (n : ℕ) (labels : Fin n → Fin (m + 1))
      (hlt : ∀ i, labels i < j) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (d.dust \ ⋃ i, (T i).exclusions)
          (circleBandGraph d.quotientDomain (T j).coordinate.quotient)
          (fun i => circleBandGraph d.quotientDomain (T i).coordinate.quotient) labels) = 0 := by
    have hn := scalar_seed_ordered_compatibility d.quotientDomain d.dust
      (fun i => (T i).coordinate.quotient) (fun i => hc i.val)
      (fun i k hik => hpairs i.val k.val (fun h => hik (Fin.ext h))) j n labels hlt
    exact measure_mono_null (freeComponentFailure_mono_free sdiff_subset _ _ labels) hn
  obtain ⟨M⟩ := exists_retained_real_circle_model hcross hplane hcoarea hLusin hsard hsch
    hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    d hU hconn hG hdisj π hπ hclosed hsurj hr he hdust hne hinftyU hB hTD hBU hdense
    hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE hinfStar B hfar hBimage D
    hnest hshrink hED hfiber harcs C hC hderiv hstandard hpath ω hω hωsum hdual hlift
    T rfl hT
  have hQT : (fun i : Fin m => (T i.succ).coordinate) = Q := by
    funext i
    simp only [T, c, Fin.val_succ, finiteScalarSeedTests, dite_eq_left i.isLt]
    rfl
  exact ⟨hQT ▸ M.select Fin.succ⟩

end CircleDomainRigidity

end

end OAI
