import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformFiniteMean

namespace OAI

/-! A finite charted phase family with its actual solvers and amplitudes,
packaged for assembling different coordinate patches on one surface. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

structure ChartedMeanFamilyData {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε τ : ℝ) (s : ℝ≥0) (r ρ R : ℝ) (reference : SmallModes.Base → Tensor) where
  G : Base → Space
  smoothG : ContDiff ℝ ∞ G
  phase : Fin 3 → Base → ℝ
  support : Fin 3 → Compacts Base
  solver : ∀ j, PolynomialSolveData P ε G smoothG (phase j) (support j) τ s
  data : ∀ j, ChartedMeanData (solver j) r ρ R reference

namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def mean (d : ChartedMeanFamilyData P ε τ s r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) : (SmallModes.Base → Tensor) → SmallModes.Base → Tensor :=
  chartedFamilyMean d.data hρ δ q

def Fits (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (p : Fin 3 → ChartedMeanProfile P) : Prop := ∀ j, (p j).Fits (d.data j)

lemma mean_smooth (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.mean hρ δ q f) := chartedFamilyMean_smooth d.data hρ δ q f

/-- The actual zero-phase tensor of the finite free family in original coordinates. -/
def quadraticMean (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  combinedQuadraticMean P ε d.G d.phase
    (fun j => (d.data j).freeAmplitude hρ δ q f) τ 0

end ChartedMeanFamilyData

theorem uniform_chartedFamilyData_majorants {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : Fin 3 → ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q : ℕ) :
    ∃ β κ : ℕ → ℝ → ℝ, ∀ {ε τ : ℝ} {s : ℝ≥0} {r : ℝ}
      {reference : SmallModes.Base → Tensor} (d : ChartedMeanFamilyData P ε τ s r ρ R reference),
      d.Fits p → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r
        (tensorOrder P + 1 + (q+1)*(tensorOrder P+1))
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (d.mean hρ δ q)) β κ := by
  obtain ⟨β,κ,h⟩ := uniform_charted_family_majorants (R := R) p hρ q
  refine ⟨β,κ,?_⟩
  intro ε τ s r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ
  exact h d.data hd hτ hs hτs hs1 hε hε1 hsmall δ hδ

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
