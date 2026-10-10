import OAI.Analysis.FreeEntropy.MatrixTestPolynomial

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem integral_heatLaw_eq {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ] {s : ℝ} (hs : 0<s)
    (f : MatrixCoordinates n d → E) (hf : Continuous f) :
    (∫a,f a ∂matrixHeatLaw μ s) = ∫z,f (heatCoordinates z.1 s z.2) ∂μ.prod (productGaussian (MatrixIndex n d)) := by
  rw [matrixHeatLaw_eq hd μ hs]
  exact integral_map (heatCoordinates_continuous s).measurable.aemeasurable hf.aestronglyMeasurable
 theorem integrable_heatLaw_iff {E : Type u2} [NormedAddCommGroup E]
    (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ] {s : ℝ} (hs : 0<s)
    (f : MatrixCoordinates n d → E) (hf : Continuous f) :
    Integrable f (matrixHeatLaw μ s) ↔ Integrable (fun z => f (heatCoordinates z.1 s z.2)) (μ.prod (productGaussian (MatrixIndex n d))) := by
  rw [matrixHeatLaw_eq hd μ hs]
  exact integrable_map_measure hf.aestronglyMeasurable (heatCoordinates_continuous s).measurable.aemeasurable
 theorem matrixHeatLaw_moment_integrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R s : ℝ} (hR : 0 ≤ R) (hμ : ∀ᵐa ∂μ,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R) (hs : 0<s) (w : List (Fin n)) :
    Integrable (fun a => matrixMoment a w) (matrixHeatLaw μ s) :=
  (integrable_heatLaw_iff hd μ hs _ (matrixMoment_continuous w)).mpr (heatMoment_integrable hd μ hR hμ s w)
 theorem matrixHeatLaw_product_integrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R s : ℝ} (hR : 0 ≤ R) (hμ : ∀ᵐa ∂μ,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R) (hs : 0<s) (v w : List (Fin n)) :
    Integrable (fun a => matrixMoment a v*matrixMoment a w) (matrixHeatLaw μ s) := by
  apply (integrable_heatLaw_iff hd μ hs _ ((matrixMoment_continuous v).mul (matrixMoment_continuous w))).mpr
  exact complex_mul_integrable_of_squares _
    (((matrixMoment_continuous v).comp (heatCoordinates_continuous s)).aestronglyMeasurable)
    (((matrixMoment_continuous w).comp (heatCoordinates_continuous s)).aestronglyMeasurable)
    (heatMoment_power_integrable hd μ hR hμ s v 2) (heatMoment_power_integrable hd μ hR hμ s w 2)
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  {R : ℝ} (hR : 0 ≤ R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hsigma : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hD0 hD hX hR hn hσ hsigma hμ
 theorem matrixHeatLaw_moment_tendsto {s : ℝ} (hs : 0<s) (w : List (Fin n)) :
    Tendsto (fun k => ∫a,matrixMoment a w ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) w)) := by
  simp_rw [integral_heatLaw_eq (hD0 _) _ hs _ (matrixMoment_continuous w)]
  exact heatMoment_product_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ s w
 theorem matrixHeatLaw_product_tendsto {s : ℝ} (hs : 0<s) (v w : List (Fin n)) :
    Tendsto (fun k => ∫a,matrixMoment a v*matrixMoment a w ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) v*
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) w)) := by
  have he (k : ℕ) := integral_heatLaw_eq (hD0 k) (μ k) hs (fun a => matrixMoment a v*matrixMoment a w) ((matrixMoment_continuous v).mul (matrixMoment_continuous w))
  simp_rw [he]
  exact heatMoment_products_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ s v w
end FreeTensor
end FiniteEntropySeparation

end

end OAI
