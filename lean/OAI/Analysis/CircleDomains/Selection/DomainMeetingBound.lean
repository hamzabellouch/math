import OAI.Analysis.CircleDomains.Probability.PointHitPairOccupation
import OAI.Analysis.CircleDomains.Probability.MeetingFatou

namespace OAI

/-! Interior meetings of two independent laws are bounded by their local
occupation energies. The geometric small-ball constant is kept explicit. -/

open Set Function Filter Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem domain_meeting_bound_of_ball_area
    (d e : PathCodeData Sphere Sphere) (hd : IsOpen d.quotientDomain)
    (he : IsOpen e.quotientDomain) (hG : e.physicalDomain = d.physicalDomain)
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
    (A : Set Sphere) (hA : IsOpen A) (hAG : A ⊆ d.physicalDomain)
    (a : ℕ → ℝ≥0) (ha : ∀ n, 0 < a n)
    (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0)) {C E : ℝ≥0∞}
    (hball : ∀ᶠ n in atTop, ∀ x ∈ A,
      σ (ball x (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2)
    (hgE : (∫⁻ x in A, g x ^ 2 ∂σ) ≤ E)
    (hhE : (∫⁻ x in A, h x ^ 2 ∂σ) ≤ E) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {p | ∃ x ∈ A, π x ∈ range p.1.val.1 ∧ π x ∈ range p.2.val.1} ≤ C * E := by
  apply measure_event_le_of_eventual_unit_integrals _ _ (fun n => codePairProximity d e A (a n))
    (fun n => measurable_codePairProximity d e hd he A hA.measurableSet (a n))
  · rintro p ⟨x, hx, hxd, hxe⟩
    obtain ⟨R, hR, hRA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hx)
    filter_upwards [hat.eventually (gt_mem_nhds hR)] with n hn
    have hcl : closedBall x (a n) ⊆ A := fun y hy =>
      hRA ((mem_closedBall.mp hy).trans_lt hn)
    have hmd := code_hit_ball_occupation_ge d hd π hπ hclosed hsurj hr hed hdend x (ha n)
      (hcl.trans hAG) p.1 hxd
    have hre : ∀ x y, π x = π y ↔ x = y ∨
        (x ∈ e.physicalDomainᶜ ∧ y ∈ connectedComponentIn e.physicalDomainᶜ x) := by
      simpa only [hG] using hr
    have hme := code_hit_ball_occupation_ge e he π hπ hclosed hsurj hre hee heend x (ha n)
      (by simpa only [hG] using hcl.trans hAG) p.2 hxe
    exact one_le_ball_pair_integral _ _ A x (ha n).ne' (ball_subset_closedBall.trans hcl) hmd hme
  · filter_upwards [hball] with n hn
    exact mean_codePairProximity_le d e hd he P Q σ g h hg hh hP hQ A hA.measurableSet
      (ha n).ne' hn hgE hhE

end CircleDomainRigidity

end

end OAI
