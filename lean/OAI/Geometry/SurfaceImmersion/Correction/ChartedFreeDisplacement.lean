import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeSeed
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors

namespace OAI

/-! The real displacement of the actual charted free amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma coordinate_originalFreeSeed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    coordinateAmplitude (c.originalFreeSeed δ q b) =
      (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b) :
        SmallModes.Field 4) := by
  funext x
  change (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b))
    (planeCoordinateIsometry (planeCoordinateIsometry.symm x)) = _
  rw [planeCoordinateIsometry.apply_symm_apply]

def freeDisplacement (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) : RField 4 :=
  QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b))

lemma freeDisplacement_smooth_support (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    ContDiff ℝ ∞ (c.freeDisplacement δ q b) ∧
      tsupport (c.freeDisplacement δ q b) ⊆ (modeSupport K : Set SmallModes.Base) := by
  unfold freeDisplacement
  rw [c.coordinate_originalFreeSeed]
  exact chart_displacement_smooth_support c.e c.smoothForward (modeSupport K) c.supportChart
    (coordinatePhase φ) (c.smoothPhase.comp planeCoordinateIsometry.symm.contDiff) τ (c.freeSeed δ q b)

def freeSizeFactor (q m : ℕ) (N : ℝ) : ℝ :=
  (m.factorial : ℝ) * 2 ^ m * correctedSeedBudget (tensorOrder P) c.C c.D q m N * c.J m ^ m

theorem freeDisplacement_bound {δ A N : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (inputOrder (P := P) q m) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (inputOrder (P := P) q m) b ≤ A) :
    WeightedBound Set.univ τ m (c.freeSizeFactor q m N * A * (δ * τ)) (c.freeDisplacement δ q b) := by
  have hz := correctedNormalSeed_bound δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hδ hτ hs hτs hs1 hε hsmall
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial q m A N hA hN hn b hb
  have hbudget := correctedSeedBudget_nonneg (tensorOrder P) c.C c.D c.nonnegC q m hN
  have hh := chart_displacement_bound c.e c.smoothForward (modeSupport K) c.supportChart
    (coordinatePhase φ) c.phase hs hτ hτs (hτs.trans (show (s : ℝ) ≤ 1 from hs1))
    (show 0 ≤ correctedSeedBudget (tensorOrder P) c.C c.D q m N * A * (δ * τ) by positivity)
    (c.oneLEJ m) (c.coordinates m) (c.freeSeed δ q b) hz
  unfold freeDisplacement
  rw [c.coordinate_originalFreeSeed]
  convert hh using 1
  unfold freeSizeFactor
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
