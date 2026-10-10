import OAI.Analysis.CircleDomains.Modulus.SimpleArcPayment
import OAI.Analysis.CircleDomains.Topology.FullIntervalTag
import OAI.Analysis.CircleDomains.Modulus.ArcBoundaryPayment
import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction

namespace OAI

/-! Restricting a simple arc to domain endpoints makes its full-interval
tag admissible. The actual barrier inequality then extends to free traces. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

section
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem raw_simple_physical_arc_domain_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hinj : Injective γ.val) (hγH : range γ.val ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ.val t) ∈ d.levels (labels i))
    (h0 : γ.val ⊥ ∈ d.quotientDomain) (h1 : γ.val ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |u (γ.val ⊤) - u (γ.val ⊥)| ≤
      4 * levelPaymentMeasure π d.physicalDomain H g m (range γ.val) := by
  let Γ : TaggedPhysicalPath d := (γ, (fullIntervalTaggedPath γ.val n labels levels).2)
  have hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2) :=
    fullIntervalTaggedPath_allowed d ν N γ.val hinj γ.property n labels levels hN hlevel
      (fun h => Set.disjoint_left.mp hdisj h0 h)
      (fun h => Set.disjoint_left.mp hdisj h1 h)
  have hcost : physicalTollCost d g m γ ≤
      levelPaymentMeasure π d.physicalDomain H g m (range γ.val) :=
    simple_arc_cost_le_own_range d hU π hπ he hH g m γ hinj hγH
  have hp : ENNReal.ofReal |u (γ.val ⊤) - u (γ.val ⊥)| ≤ 4 * physicalTollCost d g m γ :=
    hpay Γ hΓ h0 h1
  exact hp.trans (mul_le_mul_right hcost 4)

theorem raw_simple_arc_domain_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : C(PathTime, X)) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i))
    (h0 : γ ⊥ ∈ d.quotientDomain) (h1 : γ ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |u (γ ⊤) - u (γ ⊥)| ≤
      4 * levelPaymentMeasure π d.physicalDomain H g m (range γ) := by
  have hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞ :=
    (simple_quotient_arc_physical_length_le_preimage d.domainEquiv d.basePoint π he
      γ hinj hγH).trans_lt hlength
  exact raw_simple_physical_arc_domain_payment d hU hdisj π hπ he hH g m ν N u hpay
    ⟨γ, hfin⟩ hinj hγH n labels levels hN hlevel h0 h1

theorem raw_simple_arc_domain_pair_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hfinite : IsFiniteMeasure (levelPaymentMeasure π d.physicalDomain H g m))
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : C(PathTime, X)) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i)) :
    ∀p ∈ range γ ∩ d.quotientDomain, ∀q ∈ range γ ∩ d.quotientDomain,
      |u p - u q| ≤ 4 * (levelPaymentMeasure π d.physicalDomain H g m).real (range γ) := by
  let := hfinite
  let μ := levelPaymentMeasure π d.physicalDomain H g m
  have hforward : ∀a b : PathTime, a < b → γ a ∈ d.quotientDomain →
      γ b ∈ d.quotientDomain → |u (γ a) - u (γ b)| ≤ 4 * μ.real (range γ) := by
    intro a b hab ha hb
    let ρ := affineRestrictedPath a b γ
    have hρinj : Injective ρ := hinj.comp (affinePathTime_strictMono hab).injective
    have hρsub : range ρ ⊆ range γ := by
      rintro _ ⟨t, rfl⟩
      exact mem_range_self (affinePathTime a b t)
    have hρ0 : ρ ⊥ = γ a := congrArg γ (affinePathTime_zero a b)
    have hρ1 : ρ ⊤ = γ b := congrArg γ (affinePathTime_one a b)
    have hp := raw_simple_arc_domain_payment d hU hdisj π hπ he hH hlength g m ν N u
      hpay ρ hρinj (hρsub.trans hγH) n labels levels hN
      (fun t => hlevel (affinePathTime a b t)) (hρ0.symm ▸ ha) (hρ1.symm ▸ hb)
    rw [hρ0, hρ1, abs_sub_comm] at hp
    have hbound : ENNReal.ofReal |u (γ a) - u (γ b)| ≤ 4 * μ (range γ) :=
      hp.trans (mul_le_mul_right (measure_mono hρsub) 4)
    have hr := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _))).mp hbound
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, measureReal_def] using hr
  rintro p ⟨⟨a, rfl⟩, ha⟩ q ⟨⟨b, rfl⟩, hb⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact hforward a b hab ha hb
  · simpa only [sub_self, abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (measureReal_nonneg (μ := μ) (s := range γ))
  · simpa only [abs_sub_comm] using hforward b a hba hb ha

theorem raw_simple_arc_trace_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B : Set X} (hH : MeasurableSet H) (hB : IsTotallyDisconnected B)
    (hBU : Bᶜ ⊆ d.quotientDomain)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hfinite : IsFiniteMeasure (levelPaymentMeasure π d.physicalDomain H g m))
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    {x y : X} (γ : Path x y) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i))
    {a b : ℝ} (ha : Tendsto u (𝓝[d.quotientDomain] x) (𝓝 a))
    (hb : Tendsto u (𝓝[d.quotientDomain] y) (𝓝 b)) :
    |a - b| ≤ 4 * (levelPaymentMeasure π d.physicalDomain H g m).real (range γ) := by
  apply simple_arc_boundary_payment hB hBU γ hinj u ha hb
  exact raw_simple_arc_domain_pair_payment d hU hdisj π hπ he hH hlength g m hfinite
    ν N u hpay γ.toContinuousMap hinj hγH n labels levels hN hlevel

end
end CircleDomainRigidity

end

end OAI
