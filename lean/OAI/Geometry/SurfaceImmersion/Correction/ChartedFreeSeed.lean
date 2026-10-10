import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveData
import OAI.Geometry.SurfaceImmersion.Atlas.CorrectedSeedCoordinates

namespace OAI

/-! The free geometric amplitude in the original coordinates. The same
actual polynomial operator is conjugated into the phase chart, and the
resulting amplitude is transported back with controlled derivative loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma RealModeDomain.of_complex {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : ModeDomain (fun p => complexify (F p)) U) :
    RealModeDomain F U := by
  refine ⟨h.isOpen, ?_, ?_⟩
  · intro p hp hz
    have hd := h.determinant p hp
    rw [coordDeriv_complexify (hF.differentiable (by simp) p),
      coordDeriv_complexify (hF.differentiable (by simp) p), complexify_gram, hz,
      Complex.ofReal_zero] at hd
    exact hd rfl
  · intro p hp hz
    have hg := h.good p hp
    rw [← complexify_realSecond hF, hz] at hg
    simp only [complexify, map_zero, dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hg
    exact hg rfl

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open WeightedEstimates RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

abbrev chartCompact : Compacts SmallModes.Base := chartSupport c.e (modeSupport K) c.supportChart

abbrev realMap : RealModes.RField 4 := (G ∘ planeCoordinateIsometry.symm) ∘ c.e.symm

theorem realDomain : RealModeDomain c.realMap c.e.target := RealModeDomain.of_complex c.smoothMap c.domain

def operator : SupportedField (F := SmallModes.Ambient 4) c.chartCompact →ₗ[ℝ]
    SupportedField (F := PhaseMean.ComplexTensor) c.chartCompact :=
  phaseChartPolynomialOperator c.openO c.openU P c.smoothP hG c.mapsG K c.supportU c.smoothPhase
    τ ε c.e c.smoothForward c.smoothInverse c.supportChart

def freeSeed (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := SmallModes.Ambient 4) c.chartCompact :=
  correctedNormalSeed δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b

def originalFreeSeed (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SupportedField (F := Fin 4 → ℂ) K :=
  (supportedCoordinateEquiv planeCoordinateIsometry K).symm
    ((chartEquiv c.e c.smoothForward c.smoothInverse (modeSupport K) c.supportChart).symm
      (c.freeSeed δ q b))

lemma originalFreeSeed_sub (δ : ℝ) (q : ℕ)
    (b d : SupportedField (F := ℝ) c.chartCompact) :
    c.originalFreeSeed δ q (b - d) = c.originalFreeSeed δ q b - c.originalFreeSeed δ q d := by
  simp only [originalFreeSeed, freeSeed, correctedNormalSeed_sub, map_sub]

theorem originalFreeSeed_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q m : ℕ) {A N : ℝ}
    (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hn : WeightedBound c.e.target s (m + (q + 1) * (tensorOrder P + 1)) N (freeNormal c.realMap))
    (b : SupportedField (F := ℝ) c.chartCompact)
    (hb : supportedWeightedSeminorm c.chartCompact s (m + (q + 1) * (tensorOrder P + 1)) b ≤ A) :
    supportedWeightedSeminorm K s m (c.originalFreeSeed δ q b) ≤
      ((m.factorial : ℝ) * c.J m ^ m * correctedSeedBudget (tensorOrder P) c.C c.D q m N) * A * (δ * τ) := by
  have hz := correctedNormalSeed_bound δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) hδ hτ hs hτs hs1 hε hsmall
    c.C c.D c.nonnegC c.nonnegD c.coefficients c.operator c.polynomial q m A N hA hN hn b hb
  unfold originalFreeSeed
  rw [inverse_supportedCoordinateEquiv_norm _ _ hs]
  have hp := chartPull_bound c.e c.smoothForward (modeSupport K) c.supportChart hs hs1
    (c.oneLEJ m) (c.coordinates m) (c.freeSeed δ q b)
  apply hp.trans
  calc
    _ ≤ (m.factorial : ℝ) *
        (correctedSeedBudget (tensorOrder P) c.C c.D q m N * A * (δ * τ)) * c.J m ^ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _))
        (pow_nonneg (zero_le_one.trans (c.oneLEJ m)) _)
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
