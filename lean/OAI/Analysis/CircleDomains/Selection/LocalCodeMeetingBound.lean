import OAI.Analysis.CircleDomains.Selection.CodeDustMeetingBound
import OAI.Analysis.CircleDomains.Selection.LocalizedMeetingUnion
import OAI.Analysis.CircleDomains.Selection.DomainMeetingBound

namespace OAI

/-! The full localized meeting estimate for two original code laws: the dust
part and the physical occupation part use the same collar and budget. -/

open Set Function Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem local_code_meeting_bound
    (d e : PathCodeData Sphere Sphere) (hd : IsOpen d.quotientDomain)
    (he : IsOpen e.quotientDomain) (hG : IsOpen d.physicalDomain)
    (hGe : e.physicalDomain = d.physicalDomain) (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (hed : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hee : ∀ y : e.physicalDomain, (e.domainEquiv y).val = π y.val)
    (hdend : d.target ∉ d.quotientDomain) (heend : e.target ∉ e.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    [SigmaFinite (meanCodeOccupation d P)] [SigmaFinite (meanCodeOccupation e Q)]
    (σ : Measure Sphere) [SFinite σ] (g h : Sphere → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hP : meanCodeOccupation d P = σ.withDensity g)
    (hQ : meanCodeOccupation e Q = σ.withDensity h)
    (U D : Set Sphere) (hU : IsOpen U) (hD : D.Countable)
    (hcontacts : ∀ᵐ z ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range z.1.val.1 ∩ range z.2.val.1 ∩ d.dust ⊆ D)
    (p q : Sphere) (hp : p ∈ D ∩ (U ∩ d.dust)) (hq : q ∈ D ∩ (U ∩ d.dust)) (hpq : p ≠ q)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n) (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0))
    (C δ : ℝ≥0∞)
    (hball : ∀ᶠ n in atTop, ∀ x ∈ d.physicalDomain ∩ π ⁻¹' U,
      σ (ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in d.physicalDomain ∩ π ⁻¹' U, g x ^ 2 ∂σ) ≤ δ ^ 2)
    (hhE : (∫⁻ x in d.physicalDomain ∩ π ⁻¹' U, h x ^ 2 ∂σ) ≤ δ ^ 2)
    (hatail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ p then codeHitProbability d P x.val else 0) ≤ δ)
    (hbtail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ q then codeHitProbability e Q x.val else 0) ≤ δ) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {z | ∃ x ∈ U, x ∈ range z.1.val.1 ∧ x ∈ range z.2.val.1} ≤
        2 * δ + (1 + C) * δ ^ 2 := by
  have hcover : ∀ x ∈ U, x ∈ d.dust ∨ ∃ y ∈ d.physicalDomain ∩ π ⁻¹' U, π y = x := by
    intro x hx
    by_cases hxB : x ∈ d.dust
    · exact Or.inl hxB
    · right
      let y : d.physicalDomain := d.domainEquiv.symm ⟨x, hBU hxB⟩
      have hy : π y.val = x := by
        rw [← hed y]
        exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hBU hxB⟩)
      refine ⟨y.val, ⟨y.property, ?_⟩, hy⟩
      change π y.val ∈ U
      rw [hy]
      exact hx
  have hdust := code_dust_meeting_bound d e P Q U D hD hcontacts p q hp hq hpq hatail hbtail
  have hdomain := domain_meeting_bound_of_ball_area d e hd he hGe π hπ hclosed hsurj hr
    hed hee hdend heend P Q σ g h hg hh hP hQ (d.physicalDomain ∩ π ⁻¹' U)
    (hG.inter (hU.preimage hπ)) inter_subset_left a ha hat hball hgE hhE
  apply (localized_code_meeting_union_bound d e P Q U d.dust
    (d.physicalDomain ∩ π ⁻¹' U) π hcover hdust hdomain).trans
  apply le_of_eq
  ring

end CircleDomainRigidity

end

end OAI
