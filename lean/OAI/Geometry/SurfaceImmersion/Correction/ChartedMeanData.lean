import OAI.Geometry.SurfaceImmersion.Atlas.ChartedTrialMajorants

namespace OAI

/-! Fixed geometric and jet bounds for the actual mean map of one phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

structure ChartedMeanData {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)
    (r ρ R : ℝ) (reference : SmallModes.Base → Tensor) where
  cutoff : SupportedField (F := ℝ) c.chartCompact
  form : SmallModes.Base → Tensor →L[ℝ] ℝ
  localBounds : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap cutoff form c.e c.e.symm
  budgets : Budgets c.e.source c.e.target s c.realMap cutoff form c.e c.e.symm
  compactJets : Set LowJet
  compact : IsCompact compactJets
  subsetDomain : compactJets ⊆ c.O
  mapsJets : Set.MapsTo (lowJet G) c.U compactJets
  B : ℕ → ℝ
  F : ℕ → ℝ
  oneLEB : ∀ m, 1 ≤ B m
  nonnegF : ∀ m, 0 ≤ F m
  jetsBound : ∀ m, WeightedBound c.U s (m + tensorOrder P) (B m) (lowJet G)
  phaseBound : ∀ m v, WeightedBound c.U s (m + tensorOrder P) (F m)
    (fun x => fderiv ℝ φ x (coordinateVector v))

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

def amplitude (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) : SupportedField (F := ℝ) c.chartCompact :=
  c.trialAmplitude d.cutoff d.form d.localBounds hρ A

def mean (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  c.combinedMeanField δ q (d.amplitude hρ A)

def leading (hρ : 0 < ρ) (A : SmallModes.Base → Tensor) : SmallModes.Base → Tensor :=
  c.leadingField (d.amplitude hρ A)

def freeAmplitude (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    SupportedField (F := Fin 4 → ℂ) K := c.originalFreeSeed δ q (d.amplitude hρ A)

theorem majorants (hρ : 0 < ρ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q : ℕ) :
    ∃ β κ : ℕ → ℝ → ℝ, ∀ δ : ℝ, 0 < δ →
      MeanBounds Set.univ s reference r
        (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1))
        (rescaledMean (τ / s + ε / τ ^ tensorLoss P) (d.mean hρ δ q)) β κ :=
  c.trialMean_majorants d.cutoff d.form d.localBounds d.budgets hρ d.compact d.subsetDomain
    q d.B d.F d.oneLEB d.nonnegF hτ hs hτs hs1 hε hε1 hsmall d.mapsJets d.jetsBound d.phaseBound

lemma zero_phase_identity (hρ : 0 < ρ) {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (A : SmallModes.Base → Tensor) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (d.freeAmplitude hρ δ q A)) x +
      (fun k => quadraticMeanCoefficient (P k) ε G φ (d.freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x)) =
      δ ^ 2 • (d.leading hρ A x + d.mean hρ δ q A x) :=
  c.combined_zero_phase_identity hδ hτ q (d.amplitude hρ A) x

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
