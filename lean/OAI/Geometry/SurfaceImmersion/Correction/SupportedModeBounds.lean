import OAI.Geometry.SurfaceImmersion.Correction.SupportedModeOperators

namespace OAI

/-! Weighted seminorm bounds for the actual first geometric parametrix and
its conjugated metric residual. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma forcedModeLM_zero_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m (forcedModeLM τ hG h K hKU 0 f) ≤
      initialConstant n m B * supportedWeightedSeminorm K s (m + 1) f := by
  let C := supportedWeightedSeminorm K s (m + 1) f
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb := (weightedBound_of_supportedSeminorm s (m + 1) f).restrict_open h.isOpen
  have hv := weighted_initialAmplitude hτ h hs hτs hs1 hB hC hc
    f.contDiff.contDiffOn (V := fun _ => 0) contDiffOn_const hb
    ((weightedBound_zero U s (m + 1)).mono_const hC)
  have hg : WeightedBound Set.univ s m (initialConstant n m B * C)
      (forcedModeLM τ hG h K hKU 0 f) :=
    hv.extend_support h.isOpen
      ((forcedModeLM τ hG h K hKU 0 f).tsupport_subset.trans hKU)
      (mul_nonneg (initialConstant_nonneg _ _ hB) hC)
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (initialConstant_nonneg _ _ hB) hC) _ hg

/-- One geometric correction gains the factor `τ / s` with one derivative
of the forcing. This is the actual differential operator residual. -/
lemma geometric_defect_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ModeCoefficientBound G U s (m + 1) B)
    (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) ≤
      (τ / s) * errorConstant m B * supportedWeightedSeminorm K s (m + 1) f := by
  let C := supportedWeightedSeminorm K s (m + 1) f
  have hC : 0 ≤ C := apply_nonneg _ _
  have hb := (weightedBound_of_supportedSeminorm s (m + 1) f).restrict_open h.isOpen
  have hv := weighted_residual_modeApprox_zero hτ hG h hs hs1 hB hC
    f.contDiff.contDiffOn 0 m hc hb
  have hn : 0 ≤ errorConstant m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (errorConstant_nonneg _ hB) (div_nonneg hτ.le hs.le)) hC
  have hg : WeightedBound Set.univ s m (errorConstant m B * (τ / s) * C)
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) := by
    apply (show WeightedBound U s m (errorConstant m B * (τ / s) * C)
      (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) by
        change WeightedBound U s m (errorConstant m B * (τ / s) * C)
          (residual τ G f (modeApprox τ G (fun _ => 0) f 0))
        simpa only [Nat.add_zero, zero_add, pow_one] using hv).extend_support h.isOpen
      ((conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f).tsupport_subset.trans hKU) hn
  have hh := supportedSeminorm_le_of_weightedBound hs hn
    (conjugatedDLM τ hG K (forcedModeLM τ hG h K hKU 0 f) - f) hg
  convert hh using 1
  dsimp only [C]
  ring

end ClosedSurfaceR4.SmallModes

end

end OAI
