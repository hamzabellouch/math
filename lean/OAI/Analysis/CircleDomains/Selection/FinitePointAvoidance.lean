import OAI.Analysis.CircleDomains.Probability.PointHitOccupation
import OAI.Analysis.CircleDomains.Topology.QuotientInteriorBalls
import OAI.Analysis.CircleDomains.Sobolev.SphericalBallArea
import OAI.Analysis.CircleDomains.Probability.LocalMassVanishing
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! An L² occupation density makes every fixed finite physical-domain
point polar for a code law whose terminal point lies outside the domain. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem finite_domain_point_avoided
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hend : d.target ∉ d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂sphericalArea) < ∞)
    (z : ℂ) (hz : (z : Sphere) ∈ d.physicalDomain) :
    pathHitProbability (codePathLaw d P) (π (z : Sphere)) = 0 := by
  obtain ⟨RG, hRG, hballG⟩ := Metric.mem_nhds_iff.mp (hG.mem_nhds hz)
  obtain ⟨RA, hRA, K, hK, harea⟩ := exists_small_spherical_ball_area_bound z
  let q : ℝ := min RG RA / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hqG : q < RG := by dsimp [q]; linarith [min_le_left RG RA]
  have hqA : q < RA := by dsimp [q]; linarith [min_le_right RG RA]
  let r : ℕ → ℝ≥0 := fun n => ⟨q / ((n : ℝ) + 1), by positivity⟩
  have hrpos (n : ℕ) : 0 < r n := by change 0 < q / ((n : ℝ) + 1); positivity
  have hrq (n : ℕ) : (r n : ℝ) ≤ q := by
    change q / ((n : ℝ) + 1) ≤ q
    exact div_le_self hq.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hanti : Antitone (fun n => (r n : ℝ)) := by
    intro i j hij
    change q / ((j : ℝ) + 1) ≤ q / ((i : ℝ) + 1)
    apply div_le_div_of_nonneg_left hq.le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have ht : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => q / ((n : ℝ) + 1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul q
  let A : ℕ → Set Sphere := fun n => ball (z : Sphere) (r n)
  have hAnull : sphericalArea (⋂ n, A n) = 0 := by
    apply measure_mono_null _ (sphericalArea_singleton (z : Sphere))
    intro x hx
    have hd : dist x (z : Sphere) ≤ 0 := ge_of_tendsto ht (Eventually.of_forall fun n =>
      (show dist x (z : Sphere) < r n from mem_iInter.mp hx n).le)
    exact dist_le_zero.mp hd
  apply local_mass_vanishing sphericalArea hg henergy A (fun _ => measurableSet_ball)
    (fun i j hij => ball_subset_ball (hanti hij)) hAnull r hrpos K _ hK
  · intro n
    exact harea (r n) ((hrq n).trans_lt hqA)
  · intro n
    have hball : closedBall (z : Sphere) (r n) ⊆ d.physicalDomain := by
      apply Subset.trans _ hballG
      intro x hx
      exact (mem_closedBall.mp hx).trans_lt ((hrq n).trans_lt hqG)
    obtain ⟨hO, hOU, hpre, hpO⟩ := quotient_interior_ball d π hπ hclosed hsurj hr he
      (z : Sphere) (show 0 < (r n : ℝ) from hrpos n) hball
    have hb := mean_occupation_ge_point_hit d hU π hπ he (z : Sphere) hz
      (π '' ball (z : Sphere) (r n)) hO hOU hpO
      (ENNReal.coe_ne_zero.mpr (hrpos n).ne') ENNReal.coe_ne_top
      (δ := (r n : ℝ≥0∞)) (fun b hb => ?_) P
      (fun hh => hend (hOU (subset_closure hh)))
    · rw [hocc, hpre] at hb
      exact hb
    · rw [hpre] at hb
      have hd : (r n : ℝ) ≤ dist b (z : Sphere) := le_of_not_gt hb
      simpa only [edist_dist, dist_comm, ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hd

end CircleDomainRigidity

end

end OAI
