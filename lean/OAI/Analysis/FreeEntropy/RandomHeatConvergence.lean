import OAI.Analysis.FreeEntropy.L2Convergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation.FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hD0 hD hX hR hn hσ hs hμ
 theorem heatError_product_tendsto (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      ‖matrixMoment (heatCoordinates z.1 u z.2) w-wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop (𝓝 0) := by
  have he k := heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w
    (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)
  have heq (k : ℕ) := integral_prod _ (he k)
  simp_rw [heq]
  exact heatError_integral_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w
 theorem heatMoment_product_tendsto (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      matrixMoment (heatCoordinates z.1 u z.2) w
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)) := by
  exact complex_integral_tendsto_of_L2 _ _ _
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w _)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w)
 theorem heatMoment_products_tendsto (u : ℝ) (v w : List (Fin n)) :
    Tendsto (fun k => ∫z : MatrixCoordinates n (D k) × (MatrixIndex n (D k) → ℝ),
      matrixMoment (heatCoordinates z.1 u z.2) v*matrixMoment (heatCoordinates z.1 u z.2) w
      ∂(μ k).prod (productGaussian (MatrixIndex n (D k)))) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) v*
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w)) := by
  exact complex_integral_mul_tendsto_of_L2 _ _ _ _ _
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u v)
    (fun k => heatMoment_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u v _)
    (fun k => heatMoment_error_integrable (hD0 k) (μ k) hR ((hμ k).mono (fun a ha => ha.1)) u w _)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u v)
    (heatError_product_tendsto hD0 hD J X hX hR hn σ hσ hs μ hμ u w)
end FiniteEntropySeparation.FreeTensor

end

end OAI
