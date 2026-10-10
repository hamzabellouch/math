import OAI.Analysis.FreeEntropy.FisherLiminf

namespace OAI

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
def normalizedMatrixFisher (μ : Measure (MatrixCoordinates n d)) (s : ℝ) : ℝ :=
  classicalFisher μ (s/d)/(d:ℝ)^3
 theorem matrixHeatLaw_fisher_lower (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s) (p : Fin n → WordPolynomial n) :
    (∑i,∫a,matrixFisherTest (p i) i a ∂matrixHeatLaw μ s) ≤ normalizedMatrixFisher μ s := by
  rw [normalizedMatrixFisher,le_div_iff₀ (by positivity : (0:ℝ)<(d:ℝ)^3)]
  simp_rw [integral_matrixHeatLaw μ hs hd,mul_comm (smoothedDensity μ (s/d) _) _]
  simpa only [mul_comm] using matrix_classicalFisher_lower hd μ hK hμ (div_pos hs (by exact_mod_cast hd)) p
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  (hself : ∀i,IsSelfAdjoint (X i))
  {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hsigma : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐa ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hR hμ in

omit [∀ (k : ℕ), IsProbabilityMeasure (μ k)] in
theorem diagonalMicrostates_norm_ae [∀ (k : ℕ), IsProbabilityMeasure (μ k)] (k : ℕ) :
    ∀ᵐa ∂μ k,‖a‖≤Real.sqrt ((n:ℝ)*D k)*R := by
  filter_upwards [hμ k] with a ha
  have hb := microstates_subset_closedBall (tracialVector B N G) X R hR k (D k) ((k+1:ℝ)⁻¹) ha
  simpa only [Metric.mem_closedBall,dist_zero_right] using hb
include hD0 hD hX hself hR hn hσ hsigma hμ in
 theorem matrixHeatLaw_fisherTest_tendsto {s : ℝ} (hs : 0<s) (i : Fin n) (p : WordPolynomial n) :
    Tendsto (fun k => ∫a,matrixFisherTest p i a ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (fisherTest (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) i p)) := by
  have hb k : ∀ᵐa ∂μ k,∀i,matrixOpNorm (hermitianMatrix a i) ≤ R := (hμ k).mono (fun _ ha => ha.1)
  exact matrixFisherTest_integral_tendsto
    (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s)
    (heatTuple_selfAdjoint X (fun i => semicircularN (σ i)) hself (fun i => semicircularN_selfAdjoint (B := B) (G := G) (σ i)) s)
    (fun k => matrixHeatLaw (μ k) s)
    (fun k w => matrixHeatLaw_moment_integrable (hD0 k) (μ k) hR (hb k) hs w)
    (fun k v w => matrixHeatLaw_product_integrable (hD0 k) (μ k) hR (hb k) hs v w)
    (matrixHeatLaw_moment_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ hs)
    (matrixHeatLaw_product_tendsto hD0 hD J X hX hR hn σ hσ hsigma μ hμ hs) p i
include hD0 hD hX hself hR hn hσ hsigma hμ in
 theorem freeFisher_le_liminf_matrixFisher {s : ℝ} (hs : 0<s) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) s) ≤
      liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop := by
  obtain ⟨ξ,hξ⟩ := heat_conjugates_exist J X hX σ hσ hsigma s hs
  apply freeFisher_le_liminf_tests _ _ hξ (fun k i p => ∫a,matrixFisherTest p i a ∂matrixHeatLaw (μ k) s)
  · exact matrixHeatLaw_fisherTest_tendsto hD0 hD J X hX hself hR hn σ hσ hsigma μ hμ hs
  · intro k p
    exact matrixHeatLaw_fisher_lower (hD0 k) (μ k) (show 0≤Real.sqrt ((n:ℝ)*D k)*R by positivity)
      (diagonalMicrostates_norm_ae X hR μ hμ k) hs p
end FreeTensor
end FiniteEntropySeparation

end

end OAI
