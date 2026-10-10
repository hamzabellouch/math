import OAI.Analysis.CircleDomains.Probability.PointHitOccupation
import OAI.Analysis.CircleDomains.Topology.QuotientInteriorBalls
import OAI.Analysis.CircleDomains.Probability.CodePairOccupation

namespace OAI

/-! A common interior visit forces a unit lower bound for every sufficiently
small proximity integral. The bound concerns the original physical occupations. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem one_le_ball_pair_integral {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ ν : Measure Y) [SFinite ν] (A : Set Y) (p : Y)
    {a : ℝ≥0} (ha : a ≠ 0) (hball : ball p a ⊆ A)
    (hμ : (a : ℝ≥0∞) ≤ μ (ball p a)) (hν : (a : ℝ≥0∞) ≤ ν (ball p a)) :
    1 ≤ ∫⁻ z, ballPairKernel A a z ∂μ.prod ν := by
  let B : Set Y := ball p a
  have hsub : B ×ˢ B ⊆ {z : Y × Y | z.1 ∈ A ∧ z.2 ∈ A ∧ dist z.1 z.2 < 2 * a} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨hball hx, hball hy, ?_⟩
    exact (dist_triangle x p y).trans_lt (by
      have hx' : dist x p < a := hx
      have hy' : dist p y < a := by
        rw [dist_comm]
        exact hy
      linarith)
  have hlow : (B ×ˢ B).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) ≤ ballPairKernel A a :=
    indicator_le_indicator_of_subset hsub (fun _ => bot_le)
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  calc
    1 = (a : ℝ≥0∞)⁻¹ ^ 2 * ((a : ℝ≥0∞) * (a : ℝ≥0∞)) := by
      rw [← pow_two, ← mul_pow, ENNReal.inv_mul_cancel ha0 ENNReal.coe_ne_top, one_pow]
    _ ≤ (a : ℝ≥0∞)⁻¹ ^ 2 * (μ B * ν B) :=
      mul_le_mul' le_rfl (mul_le_mul' hμ hν)
    _ = ∫⁻ z, (B ×ˢ B).indicator (fun _ => (a : ℝ≥0∞)⁻¹ ^ 2) z ∂μ.prod ν := by
      rw [lintegral_indicator_const (measurableSet_ball.prod measurableSet_ball),
        Measure.prod_prod]
    _ ≤ _ := lintegral_mono hlow

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem code_hit_ball_occupation_ge
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (p : Sphere) {a : ℝ≥0} (ha : 0 < a)
    (hball : closedBall p a ⊆ d.physicalDomain)
    (Γ : BasePathCode d) (hhit : π p ∈ range Γ.val.1) :
    (a : ℝ≥0∞) ≤ baseCodeOccupation d Γ (ball p a) := by
  have hp : p ∈ d.physicalDomain := hball (mem_closedBall_self a.coe_nonneg)
  obtain ⟨hO, hOU, hpre, hpO⟩ := quotient_interior_ball d π hπ hclosed hsurj hr he
    p (show 0 < (a : ℝ) from ha) hball
  have h := point_hit_occupation_lower_bound d hU π hπ he p hp
    (π '' ball p a) hO hOU hpO
    (ENNReal.coe_ne_zero.mpr ha.ne') ENNReal.coe_ne_top
    (δ := (a : ℝ≥0∞)) (fun b hb => ?_) (baseCodePhysicalPath d Γ)
    (by change Γ.val.1 ⊤ ∉ π '' ball p a
        rw [Γ.property.2.1.2.1]
        exact fun ht => hend (hOU (subset_closure ht))) hhit
  · simpa only [hpre, baseCodeOccupation] using h
  · rw [hpre] at hb
    have hd : (a : ℝ) ≤ dist b p := le_of_not_gt hb
    simpa only [edist_dist, dist_comm, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal hd

end CircleDomainRigidity

end

end OAI
