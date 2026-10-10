import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeDisplacement

namespace OAI

/-! The actual free displacement solves the full metric/polynomial
linearization to arbitrary finite order, in the original coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

def freeResidual (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := ComplexTensor) c.chartCompact :=
  ((SmallModes.conjugatedDLM τ (contDiff_complexify c.smoothMap) c.chartCompact).restrictScalars ℝ +
    c.operator) (c.freeSeed δ q b)

def freeInitialFactor (m : ℕ) : ℝ := max (SmallModes.fullErrorConstant 4 m (c.C m))
  (c.D m * SmallModes.initialConstant 4 (m + tensorOrder P) (c.C (m + tensorOrder P)))

def freeChartResidualFactor (q m : ℕ) (N : ℝ) : ℝ :=
  FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ c.freeInitialFactor q m *
    (Real.sqrt 2 * 2 ^ (inputOrder (P := P) q m) * N)

def freeResidualFactor (q m : ℕ) (N : ℝ) : ℝ :=
  tensorChartBudget m (c.J m) (c.J (m + 1)) * 2 ^ m * c.freeChartResidualFactor q m N

theorem freeResidual_bound {δ A N : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (q m : ℕ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (inputOrder (P := P) q m) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (inputOrder (P := P) q m) b ≤ A) :
    supportedWeightedSeminorm c.chartCompact s m (c.freeResidual δ q b) ≤
      (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * c.freeChartResidualFactor q m N * A * (δ * τ) := by
  let V := supportedFreeSeed δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) b
  have hv := supportedFreeSeed_isFree δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) b
  have hr := SmallModes.perturbedFreeMode_residual_bound τ (contDiff_complexify c.smoothMap)
    (c.realDomain.complexDomain c.smoothMap) c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hτ hs hτs hs1 hε
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial V
    hv.perpX hv.perpY hv.perpSecond q m
  rw [← SmallModes.perturbedFreeLM_apply] at hr
  change supportedWeightedSeminorm c.chartCompact s m (c.freeResidual δ q b) ≤
    (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
      FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ
        (fun r => c.freeInitialFactor r * supportedWeightedSeminorm c.chartCompact s
          (r + (tensorOrder P + 1)) V) q m at hr
  rw [FiniteParametrix.boundProfile_terminal (tensorOrder P + 1) c.κ c.freeInitialFactor
    (fun r => supportedWeightedSeminorm c.chartCompact s r V) q m] at hr
  have hseed := supportedFreeSeed_bound c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) b hδ hτ.le hs hA hN
    (inputOrder (P := P) q m) hb hn
  have hγ (j : ℕ) : 0 ≤ c.freeInitialFactor j :=
    (SmallModes.fullErrorConstant_nonneg 4 j (c.nonnegC j)).trans (le_max_left _ _)
  have hp := FiniteParametrix.boundProfile_nonneg (L := tensorOrder P + 1) c.κ_nonneg hγ q m
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  apply hr.trans
  calc
    _ ≤ (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
        (FiniteParametrix.boundProfile (tensorOrder P + 1) c.κ c.freeInitialFactor q m *
          ((Real.sqrt 2 * 2 ^ (inputOrder (P := P) q m) * A * N) * (δ * τ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hseed hp) (pow_nonneg hη _)
    _ = _ := by unfold freeChartResidualFactor; ring

lemma freeResidual_identity (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact)
    {y : SmallModes.Base} (hy : y ∈ c.e.target) :
    pullbackField c.e.symm y (coordinateFullLinearized P ε G (c.freeDisplacement δ q b) (c.e.symm y)) =
      realOsc τ (c.freeResidual δ q b) y := by
  unfold freeDisplacement
  rw [c.coordinate_originalFreeSeed,
    phaseChartFullLinearization c.openO c.openU P c.smoothP hG c.mapsG K c.supportU
      c.smoothPhase τ ε c.e c.smoothForward c.smoothInverse c.supportChart c.phase (c.freeSeed δ q b) hy]
  rfl

theorem freeDisplacement_residual_bound {δ A N : ℝ} (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (q m : ℕ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (inputOrder (P := P) q m) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (inputOrder (P := P) q m) b ≤ A) :
    WeightedBound Set.univ τ m
      ((τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * c.freeResidualFactor q m N * A * (δ * τ))
      (coordinateFullLinearized P ε G (c.freeDisplacement δ q b)) := by
  let E := (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) * c.freeChartResidualFactor q m N * A * (δ * τ)
  have hb' := c.freeResidual_bound hδ hτ hs hτs hs1 hε q m hA hN hn b hb
  have hE : 0 ≤ E := (apply_nonneg _ _).trans hb'
  have hw := RealModes.weighted_realOsc isOpen_univ hτ hτs hE (c.freeResidual δ q b).contDiff.contDiffOn
    ((weightedBound_of_supportedSeminorm s m (c.freeResidual δ q b)).mono_const hb')
  have hr : WeightedBound c.e.target τ m (2 ^ m * E)
      (fun y => pullbackField c.e.symm y
        (coordinateFullLinearized P ε G (c.freeDisplacement δ q b) (c.e.symm y))) :=
    (hw.restrict_open c.e.open_target).congr (fun y hy => c.freeResidual_identity δ q b hy)
  have hsm : ContDiffOn ℝ ∞ (fun y => pullbackField c.e.symm y
      (coordinateFullLinearized P ε G (c.freeDisplacement δ q b) (c.e.symm y))) c.e.target :=
    (RealModes.contDiffOn_realOsc (c.freeResidual δ q b).contDiff.contDiffOn τ).congr
      (fun y hy => c.freeResidual_identity δ q b hy)
  have hsupport := ((coordinateFullLinearized_tsupport P ε G (c.freeDisplacement δ q b)).trans
    (c.freeDisplacement_smooth_support δ q b).2).trans c.supportChart
  have hτ1 : τ ≤ 1 := hτs.trans (show (s : ℝ) ≤ 1 from hs1)
  have hfield := RealModes.weighted_coordDeriv_of_jets c.e.open_source c.smoothForward hτ.le hτ1
    (zero_le_one.trans (c.oneLEJ (m + 1))) (c.coordinates (m + 1))
  have hh := weighted_residual_from_chart c.e c.smoothForward c.smoothInverse hsupport hτ hτ1
    (show 0 ≤ 2 ^ m * E by positivity) (c.oneLEJ m)
    (zero_le_one.trans (c.oneLEJ (m + 1))) (c.coordinates m) hfield hsm hr
  convert hh using 1
  unfold freeResidualFactor E
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
