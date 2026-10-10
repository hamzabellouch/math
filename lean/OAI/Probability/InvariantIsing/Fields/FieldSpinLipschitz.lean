import OAI.Probability.InvariantIsing.Magnetic.MagneticCurvatureBound

namespace OAI

/-! The actual conditional spin mean is spatially one-Lipschitz,
uniformly in the number and variances of the finite field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarLogCoshMean_dist_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (x y : ℝ) :
    |fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh x -
      fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y| ≤ |x - y| := by
  have hd z := hasDerivAt_fieldScalarLogCoshMean L hL z
  have hb (z : ℝ) :
      ‖fieldScalarSecond L (fun z => Real.log (Real.cosh z)) Real.tanh
        (fun z => 1 / (Real.cosh z) ^ 2) z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (fieldScalarLogCoshSecond_pos L hL z)]
    exact (fieldScalarLogCoshSecond_le_spin_variance L hL hζ z).trans
      (sub_le_self _ (sq_nonneg _))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (univ : Set ℝ)) (C := 1)
    (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hb z)
    convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using hh

end InvariantIsing

end

end OAI
