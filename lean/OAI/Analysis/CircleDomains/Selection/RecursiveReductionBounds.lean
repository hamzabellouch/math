import OAI.Analysis.CircleDomains.Topology.RecursiveCompactReduction
import OAI.Analysis.CircleDomains.Topology.PhysicalBoundaryGate

namespace OAI

/-! The compact recursive law supplies the quantitative hypotheses used by the mean
construction: finite physical energy, square-summable actual hit weights, and the lower
bound imposed by its original physical collar gate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
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

 theorem hit_probability (x : Sphere) :
    pathHitProbability (Q.law.map Subtype.val) x =
      (Q.law : Measure Q.arcs) {γ | x ∈ range γ.val} := by
  rw [pathHitProbability, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe (isClosed_paths_hitting x).measurableSet]
  rfl

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem density_energy_finite :
    (∫⁻ x, Q.density x ^ 2 ∂sphericalArea) < ∞ := by
  apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp
  exact ((le_add_right le_rfl).trans_lt Q.small).trans_le le_top

 theorem hit_square_summable :
    Summable (fun s : L.data.dust => ((Q.law : Measure Q.arcs).real {γ | s.val ∈ range γ.val}) ^ 2) := by
  have hr (x : Sphere) : pathHitReal (Q.law.map Subtype.val) x ≤
      2 * pathHitReal (codePathLaw L.data L.law) x := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top (by norm_num)
        (pathHitProbability_le_one (codePathLaw L.data L.law) x))) (Q.hit_le x)
    simpa only [pathHitReal, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have ht : Summable (fun s : L.data.dust => pathHitReal (Q.law.map Subtype.val) s.val ^ 2) := by
    apply summable_of_sum_le (fun _ => sq_nonneg _) (c := (2 * L.hitConstant) ^ 2)
    intro F
    calc
      _ ≤ ∑ s ∈ F, (2 * pathHitReal (codePathLaw L.data L.law) s.val) ^ 2 := by
        apply Finset.sum_le_sum
        intro s _
        exact pow_le_pow_left₀ (pathHitReal_nonneg _ _) (hr s.val) 2
      _ = 4 * ∑ s ∈ F, pathHitReal (codePathLaw L.data L.law) s.val ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ ≤ 4 * L.hitConstant ^ 2 := mul_le_mul_of_nonneg_left (L.finite_hit_tests F) (by norm_num)
      _ = _ := by ring
  exact ht.congr (fun s => congrArg (fun t : ℝ≥0∞ => t.toReal ^ 2) (Q.hit_probability s.val))

 theorem physical_start_distance
    (hC : ∀ n, IsClosed (L.data.gateContours n)) (hK : ∀ n, IsClosed (L.data.gateSets n))
    (n : ℕ) (hfront : frontier V ⊆ L.data.gateContours n)
    (f : L.data.quotientDomain → Sphere) (W : Set Sphere)
    (hgate : L.data.gateSets n = Subtype.val '' (f ⁻¹' closure W))
    (F₀ : ℂ → ℂ)
    (hF : ∀ x : L.data.quotientDomain,
      f x = (F₀ (finiteCoord (physicalValue L.data.domainEquiv L.data.basePoint x.val)) : Sphere))
    (c : ℂ) (r : ℝ≥0) (δ : ℝ)
    (hgap : ∀ z : ℂ, (z : Sphere) ∈ closure W → δ ≤ Metric.infDist z (closedBall c (r : ℝ))) :
    ∀ᵐ γ : Q.arcs ∂(Q.law : Measure Q.arcs),
      δ ≤ Metric.infDist
        (F₀ (finiteCoord (physicalValue L.data.domainEquiv L.data.basePoint (γ.val 0))))
        (closedBall c (r : ℝ)) := by
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
