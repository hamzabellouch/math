import OAI.Probability.InvariantIsing.Haar.HaarHeatOscillation
import OAI.Probability.InvariantIsing.Haar.HaarHeatMean
import OAI.Probability.InvariantIsing.Haar.HaarHeatOrder

namespace OAI

/-! Convergence of the actual orthogonal polynomial heat flow to its Haar mean. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter
open scoped Topology
namespace InvariantIsing

theorem haarPolynomialHeat_tendsto_mean {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (U : SpecialOrthogonal N) :
    Tendsto (fun t : ℝ => haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)
      atTop (𝓝 (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)) := by
  let u (t : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue
    ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) V
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hub (t : ℝ) (ht : 0 ≤ t) (V : SpecialOrthogonal N) : |u t V| ≤ B := by
    apply abs_le.mpr
    apply haarPolynomialHeat_bounds p (-B) B
    · intro W
      exact (abs_le.mp (hB W)).1
    · intro W
      exact (abs_le.mp (hB W)).2
    · exact ht
  have hlim : Tendsto (fun t : ℝ => ∫ V, u t V-u t U ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := fun t V => u t V-u t U) (f := fun _ => (0:ℝ)) (fun _ => 2*B)
    simp only [integral_zero] at h
    apply h
    · exact Eventually.of_forall fun t =>
        ((continuous_haarPolynomialValue _).sub continuous_const).measurable.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      exact ae_of_all μ fun V => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hub t ht V,hub t ht U])
    · exact integrable_const _
    · exact ae_of_all μ fun V => haarPolynomialHeat_difference_tendsto hN p V U
  have he (t : ℝ) : (∫ V, u t V-u t U ∂μ) =
      (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-u t U := by
    rw [integral_sub (haarPolynomialValue_integrable _ μ) (integrable_const _),
      integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [haarPolynomialHeat_mean]
  simp_rw [he] at hlim
  have hh : Tendsto (fun t : ℝ => (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-
      ((∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-u t U)) atTop
      (𝓝 ((∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-0)) :=
    tendsto_const_nhds.sub hlim
  simpa only [sub_sub_cancel,sub_zero] using hh

end InvariantIsing

end

end OAI
