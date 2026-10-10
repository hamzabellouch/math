import OAI.Analysis.CircleDomains.Modulus.BarrierConstruction
import OAI.Analysis.CircleDomains.Modulus.PerturbedBarrierData
import OAI.Analysis.CircleDomains.Modulus.ModulusNormBound

namespace OAI

/-! Failure of a small actual compatible barrier gives a uniform lower
bound on every admissible coding metric. The excluded tuples and positive
perturbations are constructed from that metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def barrierConstructionConstant (C : ℝ) : ℝ≥0∞ :=
  max (2 * ENNReal.ofReal (4 * (9 * C))) 4

theorem barrierConstructionConstant_ne_top (C : ℝ) : barrierConstructionConstant C ≠ ∞ := by
  apply ne_of_lt
  exact max_lt_iff.mpr ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top, by norm_num⟩

variable [MeasurableSpace C(PathTime, Sphere)]

theorem trial_metric_norm_lower_bound
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
    (ν : Measure Sphere) [NullSingletonClass ν]
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
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
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
    (h : PathCostSpace Sphere A → ℝ≥0∞) (hh : Measurable h)
    (heh : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c (tupleReference ω)) < ∞)
    (hadm : CostAdmissible d a c ν h)
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize) :
    β ≤ 2 * barrierConstructionConstant C *
      squareIntegralNorm (pathCostReference sphericalArea c (tupleReference ω)) h := by
  let K := barrierConstructionConstant C
  have hK : K ≠ ∞ := barrierConstructionConstant_ne_top C
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hpos : 0 < (ε : ℝ≥0∞) := ENNReal.coe_pos.mpr hε
  have hKadd : 2 + K ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hK⟩
  obtain ⟨η, hη, hηsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hKadd hpos.ne'
  obtain ⟨δ, g, m, hδ, hg, hpositive, hge, hme, hmoff, hsize, hcost⟩ :=
    exists_perturbed_barrier_data d a ha c hc ν (tupleReference ω) h hh hadm heh
      (ENNReal.coe_pos.mpr hη) ENNReal.coe_ne_top
  let N := tupleInfiniteExclusions (h ∘ costTuple)
  have hN (n : ℕ) (labels : Fin (n + 1) → ℕ) :
      (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))) (N n labels) = 0 :=
    null_tupleExclusions_of_reference_energy sphericalArea c ω hω h hh heh n labels
  have hm : ∀x ∈ d.quotientDomain, m x = 0 := by
    intro x hx
    apply hmoff
    intro hxa
    exact Set.disjoint_left.mp hdisj hx (haB hxa)
  have hunit (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
      (hallowed : AllowedTaggedPath d ν N (ρ.val, θ)) (hstart : ρ.val ⊥ ∈ d.anchor)
      (hend : ρ.val ⊤ = p) (hfirst : ∀t < (⊤ : PathTime), ρ.val t ≠ p)
      (hgate : GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val) :
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m := by
    apply hcost ρ θ
    refine ⟨hallowed, ⟨hstart, ?_⟩, ?_⟩
    · rw [htarget]
      exact ⟨hend, hfirst⟩
    · simpa only [hcontours, hgates] using hgate
  obtain ⟨R, hR⟩ := exists_controlled_compatible_real_barrier
    hcoarea hLusin hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he
    hB hTD hBU hdense hinfty hbad ν N hinf EStar hE hEU hEStar hEStarE hinfE
    p hpDust hp D hnest hshrink hED f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg hge m hm hme.ne
    (δ : ℝ≥0∞) (ENNReal.coe_pos.mpr hδ).ne' (fun y _ => hpositive y) hpoint hunit
    hfiber harcs previous hlevels hweights hN flags hflags C hC hderiv
    (ENNReal.coe_pos.mpr hη) ENNReal.coe_ne_top
  refine (hno R).trans (hR.trans ?_)
  calc
    2 * (↑η + ENNReal.ofReal (4 * (9 * C)) * squareIntegralNorm sphericalArea g) +
        4 * countingSquareNorm m =
      2 * ↑η + (2 * ENNReal.ofReal (4 * (9 * C))) * squareIntegralNorm sphericalArea g +
        4 * countingSquareNorm m := by ring
    _ ≤ 2 * ↑η + K * squareIntegralNorm sphericalArea g + K * countingSquareNorm m := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul' (le_max_left _ _) le_rfl))
        (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = 2 * ↑η + K * (squareIntegralNorm sphericalArea g + countingSquareNorm m) := by ring
    _ ≤ 2 * ↑η + K * (2 * squareIntegralNorm
        (pathCostReference sphericalArea c (tupleReference ω)) h + ↑η) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hsize)
    _ = 2 * K * squareIntegralNorm (pathCostReference sphericalArea c (tupleReference ω)) h +
        ↑η * (2 + K) := by ring
    _ ≤ _ := add_le_add le_rfl hηsmall.le

end CircleDomainRigidity

end

end OAI
