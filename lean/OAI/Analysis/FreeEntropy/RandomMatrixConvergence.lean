import OAI.Analysis.FreeEntropy.UniformConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem heatCoordinates_continuous {n d : ℕ} (u : ℝ) :
    Continuous (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => heatCoordinates z.1 u z.2) := by
  exact continuous_fst.add ((PiLp.continuous_toLp 2 (fun _ : MatrixIndex n d => ℝ)).comp continuous_snd |>.const_smul (Real.sqrt u/Real.sqrt d))
 theorem conditionalHeatError_measurable {n d : ℕ} (u : ℝ) (w : List (Fin n)) (z : ℂ) :
    Measurable (fun a : MatrixCoordinates n d => ∫ x,‖matrixMoment (heatCoordinates a u x) w-z‖^2 ∂productGaussian (MatrixIndex n d)) := by
  have h : Continuous (fun z' : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z'.1 u z'.2) w-z‖^2) :=
    (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).sub continuous_const).norm.pow 2
  exact h.stronglyMeasurable.integral_prod_right'.measurable
 namespace FreeTensor
 variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {n : ℕ}
 theorem heatError_uniform {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
    {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
    (u : ℝ) (w : List (Fin n)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in atTop,∀a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k),
      |∫ x,‖matrixMoment (heatCoordinates a u x) w-
        wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k))|<ε := by
  apply uniform_of_all_selections _ hn _ _ hε
  intro a ha
  simp only [matrixMoment_heatCoordinates]
  apply heatMatrix_meanSquare_tendsto hD0 hD (fun k => hermitianMatrix (a k)) hR (fun k i => (ha k).1 i) J X hX σ hσ hs
  intro v
  exact diagonalMicrostates_moments (tracialVector B N G) X a ha v
 theorem heatError_integral_tendsto {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
    {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀i,σ i ∉ J)
    (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐ a ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
    (u : ℝ) (w : List (Fin n)) :
    Tendsto (fun k => ∫ a,∫ x,‖matrixMoment (heatCoordinates a u x) w-
      wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) w‖^2 ∂productGaussian (MatrixIndex n (D k)) ∂μ k) atTop (𝓝 0) := by
  apply integral_tendsto_zero_of_uniform μ _ hμ _ (fun k => (conditionalHeatError_measurable u w _).aestronglyMeasurable)
  intro ε hε
  exact heatError_uniform hD0 hD J X hX hR hn σ hσ hs u w hε
 end FreeTensor
end FiniteEntropySeparation

end

end OAI
