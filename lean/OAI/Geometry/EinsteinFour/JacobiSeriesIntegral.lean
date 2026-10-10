import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! Passing the finite curvature-moment bounds through the positive
logarithmic series. The dominating function is its actual pointwise sum. -/
namespace PositiveEinsteinFour.Jacobi
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_nonnegative_series_le
    (F : ℕ → Ω → ℝ) (S : Ω → ℝ) (g : ℕ → ℝ) (b : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hS : Integrable S μ)
    (hpos : ∀ n x, 0 ≤ F n x)
    (hs : ∀ x, HasSum (fun n => F n x) (S x))
    (hg : HasSum g b) (hbound : ∀ n, (∫ x, F n x ∂μ) ≤ g n) :
    (∫ x, S x ∂μ) ≤ b := by
  have hp (n : ℕ) (x : Ω) : ‖∑ i ∈ Finset.range n, F i x‖ ≤ S x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => hpos i x))]
    exact sum_le_hasSum (Finset.range n) (fun i _ => hpos i x) (hs x)
  have ht := tendsto_integral_of_dominated_convergence S
    (fun n => (integrable_finsetSum _ (fun i _ => hF i)).aestronglyMeasurable) hS
    (fun n => Filter.Eventually.of_forall (hp n))
    (Filter.Eventually.of_forall (fun x => (hs x).tendsto_sum_nat))
  apply le_of_tendsto_of_tendsto ht hg.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro n
  change (∫ x, ∑ i ∈ Finset.range n, F i x ∂μ) ≤ ∑ i ∈ Finset.range n, g i
  rw [integral_finsetSum _ (fun i _ => hF i)]
  exact Finset.sum_le_sum (fun i _ => hbound i)

end
end PositiveEinsteinFour.Jacobi

end OAI
