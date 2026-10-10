import OAI.Analysis.CircleDomains.Selection.RecursiveReductionBounds
import OAI.Analysis.CircleDomains.Probability.PhysicalLawRebasing
import OAI.Analysis.CircleDomains.Topology.SubarcPointAvoidance

namespace OAI

/-! The compact recursive law in the original base presentation. The fallback
point and the equivalent restricted homeomorphism have no effect on physical costs. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace CompactRecursiveReduction
variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  {L : RecursiveCodeLaw base π Flags ω} {V : Set Sphere} {ε : ℝ≥0∞}
  (Q : CompactRecursiveReduction L V ε)

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_finite_length
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val) :
    ∀ γ ∈ Q.arcs, physicalDomainLength base.domainEquiv base.basePoint γ < ∞ := by
  intro γ hγ
  rw [← physicalDomainLength_congr_projection L.data.domainEquiv base.domainEquiv
    L.physical_eq L.quotient_eq π L.domain_agrees he L.data.basePoint base.basePoint γ]
  exact Q.finite_length γ hγ

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_occupation
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val) :
    meanPhysicalOccupation base.domainEquiv base.basePoint (Q.law.map Subtype.val) =
      sphericalArea.withDensity Q.density := by
  rw [← meanPhysicalOccupation_congr_projection L.data.domainEquiv base.domainEquiv
    L.physical_eq L.quotient_eq π L.domain_agrees he L.data.basePoint base.basePoint]
  exact Q.occupation

 theorem base_hit_square_summable :
    Summable (fun s : base.dust => ((Q.law : Measure Q.arcs).real {γ | s.val ∈ range γ.val}) ^ 2) := by
  have h := Q.hit_square_summable
  rw [L.dust_eq] at h
  exact h

 def baseHitWeight (s : base.dust) : ℝ≥0∞ :=
    if s.val ≠ L.data.target then pathHitProbability (Q.law.map Subtype.val) s.val else 0

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem base_small :
    (∫⁻ x, Q.density x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) +
      countingSquareNorm Q.baseHitWeight < ε := by
  have h := Q.small
  rw [L.dust_eq] at h
  exact h

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem baseHitWeight_square_finite : (∑' s, Q.baseHitWeight s ^ 2) < ∞ := by
  have h : countingSquareNorm Q.baseHitWeight < ∞ :=
    ((le_add_left le_rfl).trans_lt Q.base_small).trans_le le_top
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp h

 theorem baseHitWeight_le (s : base.dust) (hs : s.val ≠ L.data.target) :
    (Q.law : Measure Q.arcs) {γ | s.val ∈ range γ.val} ≤ Q.baseHitWeight s := by
  rw [baseHitWeight, ite_eq_left hs, Q.hit_probability]

 theorem avoids_domain
    (hU : IsOpen base.quotientDomain) (hG : IsOpen base.physicalDomain)
    (hdust : base.dust = base.quotientDomainᶜ)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (x : Sphere) (hx : x ∈ base.quotientDomain) (hxi : x ≠ π OnePoint.infty) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs), x ∉ range γ.val := by
  have hout : L.data.target ∉ L.data.quotientDomain := by
    rw [L.quotient_eq]
    have hb := L.target_dust
    rw [hdust] at hb
    exact hb
  have hz := codeHitProbability_zero_off_dust L.data
    (L.quotient_eq.symm ▸ hU) (L.physical_eq.symm ▸ hG)
    (by rw [L.dust_eq, L.quotient_eq, hdust, compl_compl])
    π hπ hclosed hsurj (L.physical_eq.symm ▸ hr) L.domain_agrees hout
    L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite
    x (by rw [L.dust_eq, hdust, mem_compl_iff, not_not]; exact hx) hxi
  have havoid := Q.reduction.avoids_point (by rwa [pathHitProbability_codePathLaw])
  rw [ProbabilityMeasure.toMeasure_map] at havoid
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable havoid

 theorem physical_start_distance_base
    (hC : ∀ n, IsClosed (L.data.gateContours n)) (hK : ∀ n, IsClosed (L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n)
    (f : base.quotientDomain → Sphere) (W : Set Sphere)
    (hgate : L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF : ∀ x : base.quotientDomain,
      f x = (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0) (δ : ℝ)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W →
      δ ≤ Metric.infDist z (Metric.closedBall c (r : ℝ))) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      δ ≤ Metric.infDist
        (F₀ (finiteCoord (physicalValue base.domainEquiv base.basePoint (γ.val 0))))
        (Metric.closedBall c (r : ℝ)) := by
  filter_upwards [Q.start_gate hC hK n hfront] with γ hγ
  rw [hgate] at hγ
  obtain ⟨x, hx, hxeq⟩ := hγ
  apply hgap
  change f x ∈ closure W at hx
  rw [hF, hxeq] at hx
  exact hx

end CompactRecursiveReduction
end CircleDomainRigidity

end

end OAI
