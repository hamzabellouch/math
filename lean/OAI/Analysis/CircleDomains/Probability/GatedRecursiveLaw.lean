import OAI.Analysis.CircleDomains.Probability.PriorPositiveBarrierLaw
import OAI.Analysis.CircleDomains.Probability.RecursiveLawConstruction
import OAI.Analysis.CircleDomains.Modulus.LevelBarrierRebase
import OAI.Analysis.CircleDomains.Topology.RelativelyClosedGates

namespace OAI

/-! Failure of a small compatible real barrier constructs the recursive law
with the prescribed collar gates and actual prior-law presentation. The
code space is Borel because the gates are closed on their contours. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_gated_recursive_law_of_no_small_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀ x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hp : p ∈ d.dust)
    {g : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀ i, d.levels i = Prod.swap ⁻¹' previous.graph i)
    (hweights : ∀ i, (∑' x, d.levelWeights i x ^ 2) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ flags)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0) (hωsum : (∑' i, ω i) < ∞)
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
    (β : ℝ≥0∞) (hβ : 0 < β)
    (hno : ∀ R : CompatibleLevelBarrier d π previous flags EStar
      (fun n => (D n).region) f W₁, β ≤ R.controlledSize)
    (μ : ℕ → Measure C(PathTime, Sphere))
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    (hμ : ∀ n, (support (priorHitMass (μ n))).Countable) :
    ∃ L : RecursiveCodeLaw d π flags ω,
      L.data.target = p ∧ L.data.priorLaws = μ ∧
      L.data.gateContours = (fun n => frontier (D n).region) ∧
      L.data.gateSets = (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) := by
  let P := Classical.choice (nonempty_priorLawPresentation d.dust flags μ hflags hflagsB hμ)
  let G := RecursiveCodeGeometry.of_presentation d π he p hp P
    (fun n => frontier (D n).region) (fun _ => Subtype.val '' (f ⁻¹' closure W₂))
  let e := G.data
  let prev : PriorLevelFamily e.physicalDomain π := previous
  let : ∀ n, IsFiniteMeasure (e.priorLaws n) := hfinite
  let : Countable P.marks := P.marks_countable.to_subtype
  have hH (i : ℕ) : IsClosed (e.levels i) := by
    rw [show e.levels i = d.levels i from rfl, hlevels]
    exact (previous.closed i).preimage continuous_swap
  have hcontours : ∀ n, IsClosed (e.gateContours n) := fun _ => isClosed_frontier
  have hgates : ∀ n, IsClosed (e.gateContours n ∩ e.gateSets n) := by
    intro n
    apply isClosed_contour_gate isClosed_frontier ?_ hf isClosed_closure
    exact (D n).frontier_region_subset_quotient d π hπ he
      ((D n).isOpen_region hπ hclosed hsurj hr)
  let : StandardBorelSpace (BasePathCode e) := standardBorel_basePathCode_of_inter_closed
    e hU hB hH hμ (fun i => hflags.mono (hmarked i)) hE.measurableSet hcontours hgates
  have hno' (R : CompatibleLevelBarrier e π prev flags EStar (fun n => (D n).region) f W₁) :
      β ≤ R.controlledSize := by
    have h := hno (R.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
    exact h
  obtain ⟨r, hrpos, hrbound⟩ := exists_positive_barrier_duality_parameter C hβ
  obtain ⟨Q, hQ, htest, hcount⟩ := positive_code_law_of_no_small_level_barrier
    hcoarea hLusin hsard hsch e hU hG hdisj π hπ hclosed hsurj hr he
    hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE
    p hp (fun h => hinfty (h ▸ hp)) D hnest hshrink hED f hf W₁ W₂ hW₁ hW₂ hW₁₂
    hfiber harcs prev hlevels (fun i => (hweights i).ne) hpoint flags hflags C hC hderiv
    rfl rfl rfl (fun x : P.marks => x.val) Subtype.val_injective
    (by rintro _ ⟨x, rfl⟩; exact P.marks_dust x.property)
    (hstandard e) hpath ω hω hωsum β hno' (hdual e) (hlift e)
    r hrpos hrbound hunique (by norm_num : (0 : ℝ) < 1)
  exact ⟨RecursiveCodeLaw.of_positive_candidate G ω r hrpos 1 Q hQ htest hcount,
    rfl, rfl, rfl, rfl⟩

end CircleDomainRigidity

end

end OAI
