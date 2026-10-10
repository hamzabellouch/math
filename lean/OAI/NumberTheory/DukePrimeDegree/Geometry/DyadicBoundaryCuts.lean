import OAI.NumberTheory.DukePrimeDegree.Dynamics.QuantitativeCutAverage
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Distance cuts with uniform quantitative boundary bounds

One cut controls all dyadic widths. The constant depends only on the
length of the interval from which the cut is selected, not the observable
or the probability measure.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

def dyadicBoundaryCost (μ : Measure Y) (f : Y → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal ((2:ℝ)^k) * μ (realBoundaryStrip f r ((1/4:ℝ)^k))

lemma lintegral_dyadicBoundaryCost (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) :
    (∫⁻ r, dyadicBoundaryCost μ f r) = 4 := by
  unfold dyadicBoundaryCost
  have hm (k : ℕ) : Measurable (fun r =>
      ENNReal.ofReal ((2:ℝ)^k) * μ (realBoundaryStrip f r ((1/4:ℝ)^k))) :=
    measurable_const.mul (measurable_realBoundaryStrip_mass μ hf _)
  rw [lintegral_tsum (fun k => (hm k).aemeasurable)]
  simp_rw [lintegral_const_mul _ (measurable_realBoundaryStrip_mass μ hf _),
    lintegral_realBoundaryStrip_mass μ hf]
  have he (k : ℕ) : ENNReal.ofReal ((2:ℝ)^k) * ENNReal.ofReal (2*(1/4:ℝ)^k) =
      ENNReal.ofReal (2*(1/2:ℝ)^k) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      _ = 2*((2:ℝ)^k*(1/4:ℝ)^k) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  simp_rw [he]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (summable_geometric_two.mul_left 2),tsum_mul_left,tsum_geometric_two]
  norm_num

theorem exists_dyadic_boundary_cut (μ : Measure Y) [IsProbabilityMeasure μ]
    {f : Y → ℝ} (hf : Measurable f) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, μ {x | f x=r}=0 ∧
      ∀ k : ℕ, μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
  obtain ⟨r,hr,hcost⟩ := exists_cut_cost_le (dyadicBoundaryCost μ f)
    (by norm_num : (0:ℝ)<4) hab (by rw [lintegral_dyadicBoundaryCost μ hf]; norm_num)
  have hbound (k : ℕ) : μ (realBoundaryStrip f r ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
    have hterm := (ENNReal.le_tsum k (f := fun j : ℕ =>
      ENNReal.ofReal ((2:ℝ)^j)*μ (realBoundaryStrip f r ((1/4:ℝ)^j)))).trans hcost
    have hp : 0 ≤ (1/2:ℝ)^k := by positivity
    have H := mul_le_mul' (le_rfl : ENNReal.ofReal ((1/2:ℝ)^k) ≤
      ENNReal.ofReal ((1/2:ℝ)^k)) hterm
    have he : ENNReal.ofReal ((1/2:ℝ)^k)*(ENNReal.ofReal ((2:ℝ)^k)*
        μ (realBoundaryStrip f r ((1/4:ℝ)^k))) =
        μ (realBoundaryStrip f r ((1/4:ℝ)^k)) := by
      rw [←mul_assoc,←ENNReal.ofReal_mul hp,←mul_pow]
      norm_num
    have heR : ENNReal.ofReal ((1/2:ℝ)^k)*ENNReal.ofReal (2*4/(b-a)) =
        ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k) := by
      rw [←ENNReal.ofReal_mul hp]
      congr 1
      ring
    rwa [he,heR] at H
  refine ⟨r,hr,?_,hbound⟩
  apply fiber_null_of_summable_realBoundaryStrip_mass μ
    (fun k : ℕ => (1/4:ℝ)^k) (fun _ => by positivity) r
  have hsum := ENNReal.tsum_le_tsum hbound
  have he : (∑' k : ℕ, ENNReal.ofReal (8/(b-a)*(1/2:ℝ)^k)) < ∞ :=
    (summable_geometric_two.mul_left (8/(b-a))).tsum_ofReal_lt_top
  exact (lt_of_le_of_lt hsum he).ne

end DukePrimeDegree

end

end OAI
