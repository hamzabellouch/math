import OAI.Geometry.SurfaceImmersion.Correction.PerturbedMeanDifference
import OAI.Geometry.Immersion.ClosedSurface.RealBounds

namespace OAI

/-! Supported normal seeds and the exact leading quadratic metric. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm weightedBound_of_supportedSeminorm
  supportedSeminorm_le_of_weightedBound)

lemma freeSeed_tsupport (δ τ : ℝ) (b : Base → ℝ) (F : RField 4) :
    tsupport (freeSeed δ τ b F) ⊆ tsupport b := by
  apply closure_mono
  intro p hp
  by_contra hn
  have hb : b p = 0 := by simpa only [Function.mem_support, not_not] using hn
  exact hp (by simp only [freeSeed, hb, mul_zero, Complex.ofReal_zero, zero_smul])

def supportedFreeSeed (δ τ : ℝ) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K) :
    SupportedField (F := Ambient 4) K :=
  let hs := (freeSeed_tsupport δ τ b F).trans b.tsupport_subset
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen (hs.trans hKU)
      (freeSeed_isFree hF h δ τ b.contDiff.contDiffOn).smooth)
    (subset_closure.trans hs)

lemma supportedFreeSeed_isFree (δ τ : ℝ) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K) :
    FreeCoefficient (fun p => complexify (F p)) U (supportedFreeSeed δ τ hF h K hKU b) :=
  freeSeed_isFree hF h δ τ b.contDiff.contDiffOn

lemma supportedFreeSeed_bound {δ τ : ℝ} {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K)
    {s : ℝ≥0} {B D : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hs : 0 < (s : ℝ))
    (hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ)
    (hb : supportedWeightedSeminorm K s m b ≤ B)
    (hN : WeightedBound U s m D (freeNormal F)) :
    supportedWeightedSeminorm K s m (supportedFreeSeed δ τ hF h K hKU b) ≤
      (Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ) := by
  have hh := weighted_freeSeed hF h hδ hτ hs hB hD b.contDiff.contDiffOn
    (((weightedBound_of_supportedSeminorm s m b).mono_const hb).restrict_open h.isOpen) hN
  have hn : 0 ≤ (Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ) := by positivity
  have hl : WeightedBound U s m ((Real.sqrt 2 * 2 ^ m * B * D) * (δ * τ))
      (supportedFreeSeed δ τ hF h K hKU b) := hh
  exact supportedSeminorm_le_of_weightedBound hs hn _
    (hl.extend_support h.isOpen ((supportedFreeSeed δ τ hF h K hKU b).tsupport_subset.trans hKU) hn)

lemma corrected_seed_mean (δ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K)
    (T : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Ambient 4) K)
    (v w p : Base) (hp : p ∈ U) :
    let V := supportedFreeSeed δ τ hF h K hKU b
    QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T V) w p) =
      δ ^ 2 * b p ^ 2 * v.1 * w.1 + seedMeanError τ T V V v w p := by
  dsimp only
  have hh := freeSeed_zeroPair h hτ δ b v w hp
  change QuadraticMean.zeroPair (leadingDerivative τ (supportedFreeSeed δ τ hF h K hKU b) v p)
      (leadingDerivative τ (supportedFreeSeed δ τ hF h K hKU b) w p) = _ at hh
  rw [seedMeanError, hh]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
