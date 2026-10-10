import OAI.Probability.InvariantIsing.Fields.FieldLipschitzTransport

namespace OAI

/-! The excess of the absolute field above a cutoff is a one-Lipschitz tail test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

def fieldTail (M x : ℝ) : ℝ := max (|x|-M) 0

lemma fieldTail_lipschitz (M : ℝ) : LipschitzWith 1 (fieldTail M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul,fieldTail]
  have hh := abs_max_sub_max_le_max (|x|-M) 0 (|y|-M) 0
  simp only [sub_sub_sub_cancel_right,sub_self,abs_zero] at hh
  rw [max_eq_left (abs_nonneg (|x|-|y|))] at hh
  exact hh.trans (abs_abs_sub_abs_le_abs_sub x y)

lemma fieldTail_nonneg (M x : ℝ) : 0 ≤ fieldTail M x := le_max_right _ _

lemma fieldTail_le_abs {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : fieldTail M x ≤ |x| :=
  max_le (by linarith) (abs_nonneg _)

lemma fieldTail_integral_tendsto (μ : Measure ℝ)
    (hμ : Integrable (fun x : ℝ => x) μ) :
    Tendsto (fun n : ℕ => ∫ x, fieldTail n x ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ∫ x, fieldTail n x ∂μ) atTop (𝓝 (∫ _x : ℝ, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => |x|)
    · intro n
      exact (fieldTail_lipschitz n).continuous.measurable.aestronglyMeasurable
    · exact hμ.abs
    · intro n
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (fieldTail_nonneg _ _)]
        exact fieldTail_le_abs (Nat.cast_nonneg n) x
    · apply ae_of_all
      intro x
      have he : ∀ᶠ n : ℕ in atTop, |x| ≤ (n : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |x|)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      exact (max_eq_right (sub_nonpos.mpr hn)).symm
  simpa only [integral_zero] using ht

lemma fieldTail_integral_tendsto_of_wasserstein
    (μ : ProbabilityMeasure ℝ) (μs : ℕ → ProbabilityMeasure ℝ)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hμs : ∀ n, Integrable (fun x : ℝ => x) (μs n : Measure ℝ))
    (hw : Tendsto (fun n => fieldWassersteinOne (μs n) μ) atTop (𝓝 0)) (M : ℝ) :
    Tendsto (fun n => ∫ x, fieldTail M x ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ x, fieldTail M x ∂(μ : Measure ℝ))) :=
  integral_tendsto_of_fieldWasserstein μ μs hμ hμs hw (fieldTail_lipschitz M)

end InvariantIsing

end

end OAI
