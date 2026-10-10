import OAI.Analysis.CircleDomains.Sobolev.PriorFilledSmoothBarrier
import OAI.Analysis.CircleDomains.Modulus.CompatibleLevelBarrier
import OAI.Analysis.CircleDomains.Sobolev.FilledSmoothBarrier
import OAI.Analysis.CircleDomains.Modulus.CompatibleLevelBarrier

namespace OAI

/-! The compatible barrier theorem with the enlarged flags and the full
controlled size, constructed from the actual first-arrival cost bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

theorem exists_controlled_compatible_level_barrier
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
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
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
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ d.anchor → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hN : ∀n labels, (Measure.pi (fun _ : Fin (n + 1) =>
      (volume : Measure UnitAddCircle))) (N n labels) = 0)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃ R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      R.controlledSize ≤ 2 * (ε + ENNReal.ofReal (4 * (9 * C)) *
        squareIntegralNorm sphericalArea g) + 4 * countingSquareNorm m := by
  let exceptions := flags ∪ support m
  have hcount : exceptions.Countable := hflags.union (countable_square_toll_support hm₂)
  let F := d.dust \ exceptions
  have hF : MeasurableSet F := hB.measurableSet.diff hcount.measurableSet
  have hmF : ∀x ∈ F, m x = 0 := by
    intro x hx
    by_contra hz
    exact hx.2 (Or.inr hz)
  obtain ⟨_, l, O, Q, _, hO, hOU, hEO, hfO, hzero, hone, hband, hnorm, hcompat⟩ :=
    exists_compatible_smooth_first_arrival_barrier_for_levels hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν N hinf
      d.anchor EStar hE hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
      hfiber harcs previous hlevels hweights hN F hF inter_subset_left hmF C hC hderiv hε
  have hweight : (∑'s, (4 * m s) ^ 2) < ∞ := by
    simp_rw [mul_pow]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by norm_num) hm₂.lt_top
  let R : CompatibleLevelBarrier d π previous flags EStar (fun j => (D j).region) f W₁ := {
    coordinate := Q
    level := l
    penalty := O
    penalty_open := hO
    penalty_inside := hOU
    penalty_disjoint := hEO
    penalty_avoids := hfO
    zero := hzero
    one := hone
    exclusions := exceptions
    exclusions_countable := hcount
    prior_flags := subset_union_left
    weight := fun s => 4 * m s
    weight_finite := hweight
    weight_support := fun s hs => Or.inr (fun hz => hs (by
      change 4 * m s = 0
      rw [hz, mul_zero]))
    band_bound := hband
    compatible := hcompat }
  refine ⟨R, ?_⟩
  have hA : ε + ENNReal.ofReal (4 * (9 * C)) * squareIntegralNorm sphericalArea g ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨hεfin, ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) ?_⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) henergy.ne
  have hR := R.controlledSize_le_of_partial_bounds hA hnorm
  simpa only [R, countingSquareNorm_mul] using hR

end CircleDomainRigidity

end

end OAI
