import Mathlib
import OAI.Computability.VertexCover.Analysis.OwnMeanPartialAe
import OAI.Computability.VertexCover.Analysis.VarianceCoordinateSum

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory

theorem deriv_on_resampled_fibers {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (G : (Fin n → ℝ) → Fin n → ℝ) (j : Fin n)
    (hD : ∀ᵐ s ∂law (Fin n),
      HasDerivAt (fun x => f (Function.update s j x)) (G s j) (s j)) :
    ∀ᵐ s ∂law (Fin n), ∀ᵐ x ∂intervalLaw,
      deriv (fun y => f (Function.update s j y)) x = G (Function.update s j x) j := by
  filter_upwards [VertexCover.Product.update_right_ae intervalLaw j hD] with s hs
  filter_upwards [hs] with x hx
  simp only [Function.update_idem, Function.update_self] at hx
  exact hx.deriv

theorem poincare {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : LipschitzWith 1 f)
    (G : (Fin n → ℝ) → Fin n → ℝ)
    (hGm : ∀ j, Measurable (fun s => G s j))
    (hGb : ∀ s j, |G s j| ≤ 1)
    (hD : ∀ j, ∀ᵐ s ∂law (Fin n),
      HasDerivAt (fun x => f (Function.update s j x)) (G s j) (s j)) :
    variance f (law (Fin n)) ≤ 2 * ∫ s, ∑ j, (G s j)^2 ∂law (Fin n) := by
  have hGi : ∀ j, Integrable (fun s => (G s j)^2) (law (Fin n)) := by
    intro j
    apply Integrable.of_bound ((hGm j).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hGb s j, abs_nonneg (G s j), sq_abs (G s j)]
  have hres : ∀ j, Integrable
      (fun p : (Fin n → ℝ) × ℝ => (G (Function.update p.1 j p.2) j)^2)
      ((law (Fin n)).prod intervalLaw) := fun j =>
    (VertexCover.Product.update_right_measurePreserving intervalLaw j).integrable_comp_of_integrable (hGi j)
  have hvb : ∀ j, Integrable
      (VertexCover.Product.coordinateVariance intervalLaw (boundedVersion f) j) (law (Fin n)) := by
    intro j
    exact VertexCover.Product.coordinateVariance_integrable intervalLaw (boundedVersion f)
      (boundedVersion_measurable hf.continuous.measurable) (boundedVersion_bound hf) j
  have hvi : ∀ j, Integrable
      (VertexCover.Product.coordinateVariance intervalLaw f j) (law (Fin n)) := by
    intro j
    apply (hvb j).congr
    filter_upwards [VertexCover.Product.update_right_ae intervalLaw j (boundedVersion_ae f)] with s hs
    exact variance_congr hs
  have hs : ∀ j, (∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n)) ≤
      2 * ∫ s, (G s j)^2 ∂law (Fin n) := by
    intro j
    calc
      _ ≤ ∫ s, 2 * ∫ x, (G (Function.update s j x) j)^2 ∂intervalLaw ∂law (Fin n) := by
        apply integral_mono_ae (hvi j) ((hres j).integral_prod_left.const_mul 2)
        filter_upwards [deriv_on_resampled_fibers f G j (hD j)] with s hs
        have hfs : LipschitzWith 1 (fun x => f (Function.update s j x)) := by
          simpa only [one_mul, Function.comp_def] using hf.comp (VertexCover.Product.update_lipschitz s j)
        have he : (∫ x, (deriv (fun y => f (Function.update s j y)) x)^2 ∂intervalLaw) =
            ∫ x, (G (Function.update s j x) j)^2 ∂intervalLaw := by
          apply integral_congr_ae
          filter_upwards [hs] with x hx
          rw [hx]
        simpa only [VertexCover.Product.coordinateVariance, he] using poincare_one hfs
      _ = _ := by
        rw [integral_const_mul]
        exact congrArg (fun z : ℝ => 2*z) (VertexCover.Product.integral_update_right intervalLaw j (hGi j))
  calc
    _ ≤ ∑ j, ∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n) :=
      variance_le_coordinate_sum hf
    _ ≤ ∑ j, 2 * ∫ s, (G s j)^2 ∂law (Fin n) := Finset.sum_le_sum (fun j _ => hs j)
    _ = _ := by rw [← Finset.mul_sum, integral_finsetSum _ (fun j _ => hGi j)]

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
