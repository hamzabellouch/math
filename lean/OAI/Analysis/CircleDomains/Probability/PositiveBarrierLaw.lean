import OAI.Analysis.CircleDomains.Probability.BarrierCodeLaw
import OAI.Analysis.CircleDomains.Probability.CountableExtractionFusion
import OAI.Analysis.CircleDomains.Modulus.CountablePositiveWeights

namespace OAI

/-! Full positive code law from failure of a small compatible barrier.
The countable extraction is invoked for every fusion test; the final law
keeps the quantitative occupation, fixed-mark visit, and tuple bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem positive_code_law_of_no_small_barrier
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
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hEStar_anchor : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
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
    {S : Type*} [Countable S] (a : S → Sphere) (ha : Injective a)
    (haB : range a ⊆ d.dust)
    [StandardBorelSpace (BasePathCode d)]
    (hstandard : StandardBorelProbabilityLaws (BasePathCode d))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
    (β : ℝ≥0∞)
    (hno : ∀ R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize)
    (hdual : ∀ (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode d b c ν)],
      MeasureImageDuality (ConstrainedCostCode d b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode d b c ν)],
      MeasurePlanLifting (ConstrainedCostCode d b c ν) (PathCostSpace Sphere I))
    (r : ℝ≥0) (hrpos : 0 < r)
    (hrbound : (r : ℝ≥0∞) < (β / (2 * barrierConstructionConstant C)) ^ 2)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P, CodeLawCandidate d a sphericalArea (tupleReference ω)
        (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
        (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
        (r : ℝ≥0∞)⁻¹ (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤
          (((r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1).toReal + ε) ^ 2) ∧
      {x : Sphere | x ∈ d.dust ∧
        0 < pathHitProbability (codePathLaw d P) x}.Countable := by
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hE : (r : ℝ≥0∞)⁻¹ < ∞ := ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hr0)
  let K : ℝ≥0∞ := (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1
  have hKt : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hE.ne, by simp⟩
  have hKr : ENNReal.ofReal K.toReal = K := ENNReal.ofReal_toReal hKt
  suffices hs : ∃ P, CodeLawCandidate d a sphericalArea (tupleReference ω)
      (densityMassBound sphericalArea (r : ℝ≥0∞)⁻¹)
      (densityMassBound (tupleReference ω) (r : ℝ≥0∞)⁻¹)
      (r : ℝ≥0∞)⁻¹ ((ENNReal.ofReal K.toReal) ^ 2) P ∧
      (∀ F : Finset d.dust,
        ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ (K.toReal + ε) ^ 2) ∧
      {x : Sphere | x ∈ d.dust ∧
        0 < pathHitProbability (codePathLaw d P) x}.Countable by
    simpa only [hKr] using hs
  apply positive_code_law_of_countable_extraction d hU hB hstandard hpath a ha haB
    sphericalArea (tupleReference ω) (r : ℝ≥0∞)⁻¹ hE ENNReal.toReal_nonneg _ hε
  intro I hI b hb hbB ν hν hn hνB
  let : PolishSpace I := hI.polishSpace
  let : IsFiniteMeasure ν := hν
  let : NullSingletonClass ν := hn
  obtain ⟨c, hc0, hct, _, hc⟩ := exists_positive_finite_square_weights I
  let : StandardBorelSpace (FiniteCostCode d b c) := standardBorel_finiteCostCode d hU b c
  let : StandardBorelSpace (ConstrainedCostCode d b c ν) :=
    standardBorel_constrainedCostCode d b c ν hB
  obtain ⟨P, g, q, hg, hq, hocc, hgE, hv, htuple, hqE, _, hhit, _⟩ :=
    prescribed_countable_law_of_no_small_barrier hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf
      EStar hEStar_anchor hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ hfiber harcs previous hlevels hweights hpoint flags hflags
      C hC hderiv htarget hcontours hgates b hb hbB c hc ω hω β hno hωsum
      (hdual I b c ν) (hlift I b c ν) r hrpos hrbound hc0 hct hνB hunique
  refine ⟨P, g, q, hg, hq, hocc, hgE, ?_, htuple, hqE, hhit⟩
  rw [hKr]
  exact hv

end CircleDomainRigidity

end

end OAI
