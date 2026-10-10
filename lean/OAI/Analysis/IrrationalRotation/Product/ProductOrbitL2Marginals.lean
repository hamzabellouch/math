import OAI.Analysis.IrrationalRotation.Product.ProductOrbitMarginals
import OAI.Analysis.IrrationalRotation.Analysis.RealDensityLp

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem hasUniformL2Marginals_of_average_bounds (θ : ℕ → ℝ)
    (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hw0 : ∀ l, ∀ n ∈ N l, ∀ x, 0 ≤ w l n x)
    {H : ℝ} (hH : 0 ≤ H)
    (hfirst : ∀ l, eLpNorm
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) 2 baseMeasure ≤
        ENNReal.ofReal H)
    (hsecond : ∀ l, eLpNorm
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) 2 baseMeasure ≤
        ENNReal.ofReal H) :
    HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) := by
  refine ⟨H, hH, ?_⟩
  intro l
  have hf : MemLp
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) 2 baseMeasure :=
    lt_of_le_of_lt (hfirst l) ENNReal.ofReal_lt_top
  have hg : MemLp
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) 2 baseMeasure :=
    lt_of_le_of_lt (hsecond l) ENNReal.ofReal_lt_top
  have hf0 : 0 ≤ᵐ[baseMeasure]
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) := by
    apply Filter.Eventually.of_forall
    intro x
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n hn => hw0 l n hn x))
  have hg0 : 0 ≤ᵐ[baseMeasure]
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) := by
    apply Filter.Eventually.of_forall
    intro y
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n hn => hw0 l n hn _))
  obtain ⟨f, hf0', hfEq, hfBound⟩ := DensityTransport.exists_Lp_density_of_memLp
    baseMeasure _ hf hf0 (orbitAverageMeasure_first_marginal_real θ (N l) (w l)
      (hw l) (hw0 l)) hH (hfirst l)
  obtain ⟨g, hg0', hgEq, hgBound⟩ := DensityTransport.exists_Lp_density_of_memLp
    baseMeasure _ hg hg0 (orbitAverageMeasure_second_marginal_real θ (N l) (w l)
      (hw l) (hw0 l)) hH (hsecond l)
  exact ⟨f, g, hf0', hg0', hfEq, hgEq, hfBound, hgBound⟩

end Invariant233.ProductModel.TailTrimming

end

end OAI
