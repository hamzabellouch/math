import OAI.Geometry.SurfaceImmersion.Correction.CorrectedPolynomialMean
import OAI.Geometry.SurfaceImmersion.Correction.UniformNormalizedMean
import OAI.Geometry.SurfaceImmersion.Correction.NormalizedPolynomialSupport

namespace OAI

/-! Combine the actual metric and polynomial zero-phase errors with a common
finite input order and scale-independent constants. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes

variable {n : ℕ} {U : Set Base} {O Q : Set LowJet}
variable {F : RField 4} {V : Set SmallModes.Base}

def combinedSeedMean (P : Fin n → Expression) (δ τ ε : ℝ) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (v w : SmallModes.Base) (x : Base) : ℝ :=
  normalizedPerturbedMean δ τ hF h (modeSupport K) hKV R q b v w (planeCoordinateIsometry x) +
    normalizedPolynomialMean P δ ε G firstPhase (coordinateCorrectedSeed δ τ hF h K hKV R q b) τ 0 x

lemma normalizedPerturbedMean_smooth (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (v w : SmallModes.Base) :
    ContDiff ℝ ∞ (normalizedPerturbedMean δ τ hF h (modeSupport K) hKV R q b v w) :=
  (SmallModes.seedMeanError_smooth τ
    (SmallModes.perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) (modeSupport K) hKV R q)
    (supportedFreeSeed δ τ hF h (modeSupport K) hKV b)
    (supportedFreeSeed δ τ hF h (modeSupport K) hKV b) v w).const_smul (δ⁻¹ ^ 2)

theorem combinedSeedMean_bounds
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B₀ : ℝ) (hB₀ : 1 ≤ B₀)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V) {L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G)
      (s : ℝ≥0) (δ τ ε : ℝ) (p : ℕ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      loss P ≤ p → τ / s + ε / τ ^ p ≤ 1 →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B₀ (lowJet G) →
      (∀ m, SmallModes.ReconstructionCoefficientBound (fun x => complexify (F x)) V s (m + 1) (B m)) →
      ∀ (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) s m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) s (m + L) Z) →
      WeightedBound V s (m + order P + 1 + (q + 1) * (L + 1)) N (freeNormal F) →
      ∀ (b c : SupportedField (F := ℝ) (modeSupport K)) (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + 1 + (q + 1) * (L + 1)) b ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + 1 + (q + 1) * (L + 1)) c ≤ A →
      supportedWeightedSeminorm (modeSupport K) s (m + order P + 1 + (q + 1) * (L + 1)) (b - c) ≤ A * d →
      ∀ v w : SmallModes.Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * E)
        (combinedSeedMean P δ τ ε G hF h K hKV R q b v w) ∧
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * (2 * E) * d)
        (fun x => combinedSeedMean P δ τ ε G hF h K hKV R q b v w x -
          combinedSeedMean P δ τ ε G hF h K hKV R q c v w x) := by
  obtain ⟨Ep, hEp, hpoly⟩ := correctedPolynomialMean_bounds hU hO hQ hQO P hP m B₀ 1 hB₀ zero_le_one
    hF h K hKV B D hB hD q A N hA hN
  let M := normalizedMeanBudget L B D q m N
  have hM : 0 ≤ M := normalizedMeanBudget_nonneg L B D hB q m N
  refine ⟨M * A ^ 2 + Ep, add_nonneg (mul_nonneg hM (sq_nonneg A)) hEp, ?_⟩
  intro G hG s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb hc R hR hbN b c d hd hb hcb hbc v w hv hw
  have hmOrder : m + 1 + (q + 1) * (L + 1) ≤ m + order P + 1 + (q + 1) * (L + 1) := by omega
  have hpOrder : m + order P + (q + 1) * (L + 1) ≤ m + order P + 1 + (q + 1) * (L + 1) := by omega
  have hbm := (supportedWeightedSeminorm_mono s hmOrder b).trans hb
  have hcm := (supportedWeightedSeminorm_mono s hmOrder c).trans hcb
  have hdm := (supportedWeightedSeminorm_mono s hmOrder (b - c)).trans hbc
  have hnm := hbN.mono_order hmOrder
  have hmv := normalizedMeanBudget_bound δ τ hF h (modeSupport K) hKV hδ hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m A N hA hN hnm b hbm v w hv hw
  have hmd := normalizedMeanBudget_difference δ τ hF h (modeSupport K) hKV hδ hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m A N hA hN hnm b c (A * d) (mul_nonneg hA hd) hbm hcm hdm v w hv hw
  have hsmb := normalizedPerturbedMean_smooth δ τ hF h K hKV R q b v w
  have hsmc := normalizedPerturbedMean_smooth δ τ hF h K hKV R q c v w
  have hmvc := weightedBound_comp_isometry planeCoordinateIsometry hsmb hmv
  have hmdc := weightedBound_comp_isometry planeCoordinateIsometry (hsmb.sub hsmc) hmd
  have hh := hpoly G firstPhase hG firstPhase_smooth s δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall
    hGQ hGb (firstPhase_derivative_bound U s (m + order P)) hc R hR (hbN.mono_order hpOrder)
    b c d hd ((supportedWeightedSeminorm_mono s hpOrder b).trans hb)
    ((supportedWeightedSeminorm_mono s hpOrder c).trans hcb)
    ((supportedWeightedSeminorm_mono s hpOrder (b - c)).trans hbc) 0 (by simp)
  let Zb := coordinateCorrectedSeed δ τ hF h K hKV R q b
  let Zc := coordinateCorrectedSeed δ τ hF h K hKV R q c
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hpv := normalizedPolynomialMean_extend hU firstPhase_smooth K hKU Zb δ ε τ 0
    (mul_nonneg hη hEp) hh.1
  have hpd := normalizedPolynomialMean_difference_extend hU firstPhase_smooth K hKU Zb Zc δ ε τ 0
    (by positivity) hh.2
  have hpmb := normalizedPolynomialMean_smooth hU hO hP hG firstPhase_smooth
    (fun _ hx => hQO (hGQ hx)) K hKU Zb δ ε τ 0
  have hpmc := normalizedPolynomialMean_smooth hU hO hP hG firstPhase_smooth
    (fun _ hx => hQO (hGQ hx)) K hKU Zc δ ε τ 0
  constructor
  · have hh := hmvc.add isOpen_univ.uniqueDiffOn hs.le
      (hsmb.comp planeCoordinateIsometry.contDiff).contDiffOn hpmb.contDiffOn hpv
    change WeightedBound Set.univ s m _ (combinedSeedMean P δ τ ε G hF h K hKV R q b v w) at hh
    convert hh using 1
    dsimp only [M]
    ring
  · have hh := hmdc.add isOpen_univ.uniqueDiffOn hs.le
      ((hsmb.sub hsmc).comp planeCoordinateIsometry.contDiff).contDiffOn (hpmb.sub hpmc).contDiffOn hpd
    have he := hh.congr (fun x _ => show
        combinedSeedMean P δ τ ε G hF h K hKV R q b v w x -
          combinedSeedMean P δ τ ε G hF h K hKV R q c v w x = _ by
      dsimp only [combinedSeedMean, Function.comp_apply, Pi.sub_apply]
      ring)
    convert he using 1
    dsimp only [M]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
