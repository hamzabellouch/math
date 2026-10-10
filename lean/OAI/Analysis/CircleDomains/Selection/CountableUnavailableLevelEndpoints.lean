import OAI.Analysis.CircleDomains.Probability.PriorPositiveBarrierLaw
import OAI.Analysis.CircleDomains.Selection.RecursiveEndpointCountability
import OAI.Analysis.CircleDomains.Selection.UngatedCodes
import OAI.Analysis.CircleDomains.Modulus.LevelBarrierRebase
import OAI.Analysis.CircleDomains.Modulus.UngatedBarrier

namespace OAI

/-! Countability of endpoints with no small compatible barrier. The
transfinite positive-law recursion retains all earlier laws and their dust
marks, and alternating disk crossings give the contradiction. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem countable_unavailable_endpoints_for_levels
    (hcross : UnitDiskAlternatingContinua)
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
    (P : Set Sphere) (hPB : P ⊆ d.dust)
    {g₀ : ℂ → ℝ≥0∞}
    (D : ∀ p : P, ℕ → WeightedCollar d.physicalDomain π d.dust p.val g₀)
    (hnest : ∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region)
    (hshrink : ∀ p : P, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ,
      ∀ n ≥ k, closure (D p n).region ⊆ V)
    (hED : ∀ p, Disjoint d.anchor (closure (D p 0).region))
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : PriorLevelFamily d.physicalDomain π)
    (hlevels : ∀ i, d.levels i = Prod.swap ⁻¹'
      previous.graph i)
    (hweights : ∀ i, (∑' x, d.levelWeights i x ^ 2) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility d.levels (d.dust \ flags))
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
    (hno : ∀ p : P, ∀ R : CompatibleLevelBarrier d π previous flags EStar
      (fun j => (D p j).region) (fun _ => ((0 : ℂ) : Sphere)) univ,
      β ≤ R.controlledSize) : P.Countable := by
  obtain ⟨r, hrpos, hrbound⟩ := exists_positive_barrier_duality_parameter C hβ
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevels i]
    exact (previous.closed i).preimage continuous_swap
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hωsum
  have hsmall : (P \ {OnePoint.infty}).Countable := by
    apply countable_endpoints_of_recursive_selection hcross hcoarea hsard hsch
      d π hG hU hdisj hBU hB hTD hE hEU hπ hclosed hsurj hr hbad hinfty
      flags hflags hH hweights hmarked hcompat hunique ω (P \ {OnePoint.infty})
      (fun _ hx => ⟨hPB hx.1, hx.2⟩)
    intro p hp μ hfinite hμ
    let p' : P := ⟨p, hp.1⟩
    let R := Classical.choice (nonempty_priorLawPresentation d.dust flags μ hflags hflagsB hμ)
    let G := RecursiveCodeGeometry.of_presentation d π he p (hPB hp.1) R
      (fun j => frontier (D p' j).region) (fun _ => d.quotientDomain)
    let e := G.data
    let prev : PriorLevelFamily e.physicalDomain π := previous
    let : ∀ n, IsFiniteMeasure (e.priorLaws n) := hfinite
    let : Countable R.marks := R.marks_countable.to_subtype
    have hgate : ∀ i, e.gateContours i ⊆ e.gateSets i := by
      intro i
      exact (D p' i).frontier_region_subset_quotient d π hπ he
        ((D p' i).isOpen_region hπ hclosed hsurj hr)
    let : StandardBorelSpace (BasePathCode e) := standardBorel_basePathCode_of_vacuous_gates
      e hU hB hH hμ (fun i => hflags.mono (hmarked i)) hE.measurableSet hgate
    have hno' (Q : CompatibleLevelBarrier e π prev flags EStar
        (fun j => (D p' j).region) (fun _ => ((0 : ℂ) : Sphere)) univ) :
        β ≤ Q.controlledSize := by
      have hb := hno p' (Q.rebase rfl rfl rfl rfl (fun _ => rfl) (fun _ => rfl))
      change β ≤ Q.controlledSize at hb
      exact hb
    obtain ⟨Q, hQ, htest, hcount⟩ := positive_code_law_of_no_small_level_barrier
      hcoarea hLusin hsard hsch e hU hG hdisj π hπ hclosed hsurj hr he
      hB hTD hBU hdense hinfty hbad hinf EStar hE hEU hEStar hEStarE hinfE
      p (hPB hp.1) (fun h => hinfty (h ▸ hPB hp.1)) (D p') (hnest p') (hshrink p')
      (hED p') (fun _ => ((0 : ℂ) : Sphere)) continuous_const
      univ univ isClosed_univ isOpen_univ (Subset.rfl) hfiber harcs prev hlevels
      (fun i => (hweights i).ne) hpoint flags hflags C hC hderiv rfl rfl
      (by ext i x; simp [e, G, RecursiveCodeGeometry.of_presentation, endpointCodeData])
      (fun x : R.marks => x.val) Subtype.val_injective
      (by rintro _ ⟨x, rfl⟩; exact R.marks_dust x.property)
      (hstandard e) hpath ω hω hωsum β hno' (hdual e) (hlift e)
      r hrpos hrbound hunique (by norm_num : (0 : ℝ) < 1)
    exact ⟨RecursiveCodeLaw.of_positive_candidate G ω r hrpos 1 Q hQ htest hcount, rfl, rfl⟩
  apply ((hsmall.insert OnePoint.infty)).mono
  intro p hp
  by_cases hi : p = OnePoint.infty
  · exact Or.inl hi
  · exact Or.inr ⟨hp, hi⟩

end CircleDomainRigidity

end

end OAI
