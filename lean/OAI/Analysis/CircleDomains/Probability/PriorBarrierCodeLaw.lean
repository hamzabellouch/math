import OAI.Analysis.CircleDomains.Modulus.PriorBarrierModulus
import OAI.Analysis.CircleDomains.Probability.BarrierCodeLaw
import OAI.Analysis.CircleDomains.Modulus.BarrierModulus
import OAI.Analysis.CircleDomains.Probability.CountableLawExtraction

namespace OAI

/-! Failure of a small compatible barrier yields a probability law,
using ADMS duality, Bogachev lifting, and the resulting modulus bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem code_law_of_no_small_compatible_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hωsum : (∑'i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2) :
    ∃(P : ProbabilityMeasure (BasePathCode d)) (q : PathCostSpace Sphere A → ℝ≥0∞),
      Measurable q ∧
      meanCodeCost d a c P = (pathCostReference sphericalArea c (tupleReference ω)).withDensity q ∧
      (∫⁻z, q z ^ 2 ∂pathCostReference sphericalArea c (tupleReference ω)) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), pathCostMeasure d a c Γ univ < ∞) ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hmod := hrbound.trans_le (barrier_modulus_lower_bound_for_levels hcoarea hLusin hsard hsch
    d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf
    EStar hE hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED f hf W₁ W₂
    hW₁ hW₂ hW₁₂ hfiber harcs previous hlevels hweights hpoint flags hflags C hC hderiv
    htarget hcontours hgates a ha haB c hc ω hω β hno)
  exact positive_modulus_code_law d hU hB a c ν sphericalArea (tupleReference ω)
    hc hdual hlift r hrpos hmod

theorem prescribed_countable_law_of_no_small_level_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hωsum : (∑'i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
    (hc0 : ∀s, c s ≠ 0) (hct : ∀s, c s ≠ ∞)
    (hν : ν d.dustᶜ = 0)
    (hunique : ∀x ∈ d.dust \ flags, ∀i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u) :
    ∃(P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
      Measurable g ∧ Measurable q ∧
      meanCodeOccupation d P = sphericalArea.withDensity g ∧
      (∫⁻y, g y ^ 2 ∂sphericalArea) ≤ (r : ℝ≥0∞)⁻¹ ∧
      countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤
        (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
      meanCodeTuple d P = (tupleReference ω).withDensity q ∧
      (∫⁻t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀k, slotLaw d P k ≪ tupleReference ω) ∧
      (∫⁻x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  have hmod := hrbound.trans_le (barrier_modulus_lower_bound_for_levels hcoarea hLusin hsard hsch
    d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf
    EStar hE hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED f hf W₁ W₂
    hW₁ hW₂ hW₁₂ hfiber harcs previous hlevels hweights hpoint flags hflags C hC hderiv
    htarget hcontours hgates a ha haB c hc ω hω β hno)
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevels]
    exact (previous.closed i).preimage continuous_swap
  exact prescribed_countable_law_of_positive_modulus d hU hB hH a ha c hc0 hct hc ν
    flags hflags hν hunique sphericalArea ω hωsum hdual hlift r hrpos hmod


end CircleDomainRigidity

end

end OAI
