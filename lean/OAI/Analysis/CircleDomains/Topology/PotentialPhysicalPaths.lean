import OAI.Analysis.CircleDomains.Probability.DomainPhysicalOccupation
import OAI.Analysis.CircleDomains.Selection.TaggedPhysicalRestriction
import OAI.Analysis.CircleDomains.Modulus.IntervalChartCost

namespace OAI

/-! The constructed potential controls every physical domain path. In
particular it controls ordinary chart segments with their line density. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_physical_path_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (β : RectifiablePath Y) (hβ : ∀t, β.val t ∈ d.physicalDomain) :
    ENNReal.ofReal |u (d.domainEquiv ⟨β.val ⊤, hβ ⊤⟩).val -
      u (d.domainEquiv ⟨β.val ⊥, hβ ⊥⟩).val| ≤ 4 * ∫⁻y, g y ∂pathOccupation β := by
  let γ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint β hβ
  let Γ : TaggedPhysicalPath d := (γ, fun _ => inactiveTag)
  have hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2) :=
    projected_physical_path_allowed d hdisj ν N β hβ
  have htoll : boundaryToll γ.val m = 0 := by
    have hz (t : PathTime) : m (γ.val t) = 0 :=
      hm _ (projectDomainPath_mem d.domainEquiv β.val hβ t)
    simp only [boundaryToll, hz, tsum_zero]
  have hi := hpath Γ hΓ (projectDomainPath_mem d.domainEquiv β.val hβ ⊥)
    (projectDomainPath_mem d.domainEquiv β.val hβ ⊤)
  change ENNReal.ofReal |u (d.domainEquiv ⟨β.val ⊤, hβ ⊤⟩).val -
      u (d.domainEquiv ⟨β.val ⊥, hβ ⊥⟩).val| ≤
    4 * ((∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) + boundaryToll γ.val m) at hi
  rwa [htoll, add_zero, dyadicPhysicalOccupation_project] at hi

theorem potential_chart_interval_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain) :
    ENNReal.ofReal |v (φ b) - v (φ a)| ≤
      4 * ((L : ℝ≥0∞) * ∫⁻t in Icc a b, g (φ t)) := by
  let β := intervalChartPath φ hab.le hL
  have hβ : ∀t, β.val t ∈ d.physicalDomain :=
    fun t => hdom (realIntervalPath_mem hab.le t)
  have hi := potential_physical_path_bound d hdisj ν N u g m hm hpath β hβ
  rw [← hv (β.val ⊤) (hβ ⊤), ← hv (β.val ⊥) (hβ ⊥)] at hi
  have hi' : ENNReal.ofReal |v (φ b) - v (φ a)| ≤
      4 * ∫⁻y, g y ∂pathOccupation β := by
    simpa only [β, intervalChartPath, ContinuousMap.coe_mk, Function.comp_apply,
      realIntervalPath_zero, realIntervalPath_one] using hi
  exact hi'.trans (mul_le_mul' le_rfl (intervalChartPath_cost_le φ hφ hab hL g hg))

end CircleDomainRigidity

end

end OAI
