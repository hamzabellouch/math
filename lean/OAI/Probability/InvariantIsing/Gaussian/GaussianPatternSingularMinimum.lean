import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternEuclideanNorm

namespace OAI

/-! The least singular value, as an actual unit-sphere minimum, is 1-Lipschitz. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace InvariantIsing

def gaussianPatternSingularMin {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, ‖gaussianPatternEuclideanOperator z x‖

lemma gaussianPatternSingularMin_le_add {N m : ℕ} (hm : 0 < m)
    (z w : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternSingularMin z ≤ gaussianPatternSingularMin w + ‖z-w‖ := by
  have hx : EuclideanSpace.single (⟨0,hm⟩ : Fin m) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    simp
  let : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) := ⟨⟨_,hx⟩⟩
  have hb : BddBelow (Set.range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      ‖gaussianPatternEuclideanOperator z x‖)) := ⟨0,by rintro _ ⟨x,rfl⟩; exact norm_nonneg _⟩
  have hh : gaussianPatternSingularMin z - ‖z-w‖ ≤ gaussianPatternSingularMin w := by
    apply le_ciInf
    intro x
    have hmin : gaussianPatternSingularMin z ≤ ‖gaussianPatternEuclideanOperator z x‖ := ciInf_le hb x
    have hn : ‖(x : EuclideanSpace ℝ (Fin m))‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using x.property
    have hd := abs_norm_sub_norm_le (gaussianPatternEuclideanOperator z x)
      (gaussianPatternEuclideanOperator w x)
    rw [← sub_apply,← gaussianPatternEuclideanOperator_sub] at hd
    have hbound := gaussianPatternEuclideanOperator_bound (z-w) x
    rw [hn,mul_one] at hbound
    have hdiff := (le_abs_self (‖gaussianPatternEuclideanOperator z x‖-
      ‖gaussianPatternEuclideanOperator w x‖)).trans (hd.trans hbound)
    linarith
  linarith

theorem gaussianPatternSingularMin_lipschitz (N m : ℕ) (hm : 0 < m) :
    LipschitzWith 1 (gaussianPatternSingularMin (N := N) (m := m)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have h := gaussianPatternSingularMin_le_add hm w z
    rw [norm_sub_rev] at h
    linarith
  · have h := gaussianPatternSingularMin_le_add hm z w
    linarith

end InvariantIsing

end

end OAI
