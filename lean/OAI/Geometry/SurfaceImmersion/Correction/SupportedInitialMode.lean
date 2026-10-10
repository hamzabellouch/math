import OAI.Geometry.SurfaceImmersion.Correction.SupportedModeBounds

namespace OAI

/-! Supported initial amplitudes with both forcing and a free normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma initialAmplitude_tsupport (τ : ℝ) (G V : Field n) (f : Tensor) :
    tsupport (initialAmplitude τ G V f) ⊆ tsupport V ∪ tsupport f :=
  modeApprox_tsupport τ G V f 0

def initialMode (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (V : SupportedField (F := Ambient n) K)
    (f : SupportedField (F := Fin 3 → ℂ) K) : SupportedField (F := Ambient n) K :=
  let hs := (initialAmplitude_tsupport τ G V f).trans (Set.union_subset V.tsupport_subset f.tsupport_subset)
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen (hs.trans hKU)
      (contDiffOn_initialAmplitude τ h V.contDiff.contDiffOn f.contDiff.contDiffOn))
    (subset_closure.trans hs)

lemma initialMode_apply (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (V : SupportedField (F := Ambient n) K)
    (f : SupportedField (F := Fin 3 → ℂ) K) (p : Base) :
    initialMode τ h K hKU V f p = initialAmplitude τ G V f p := rfl

lemma initialMode_free_bound (τ : ℝ) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K) :
    supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0) ≤
      initialConstant n m B * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_initialAmplitude hτ h hs hτs hs1 hB hC hc
    (f := fun _ => 0) contDiffOn_const V.contDiff.contDiffOn
    ((weightedBound_zero U s (m + 1)).mono_const hC)
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hglobal : WeightedBound Set.univ s m (initialConstant n m B * C)
      (initialMode τ h K hKU V 0) :=
    hv.extend_support h.isOpen ((initialMode τ h K hKU V 0).tsupport_subset.trans hKU)
      (mul_nonneg (initialConstant_nonneg _ _ hB) hC)
  exact supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (initialConstant_nonneg _ _ hB) hC) _ hglobal

lemma initialMode_free_difference (τ : ℝ) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : ReconstructionCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K) :
    supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) ≤
      amplitudeConstant n m B * (τ / s) * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_initialAmplitude_free_sub hτ h hs hs1 hB hC hc V.contDiff.contDiffOn
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hn : 0 ≤ amplitudeConstant n m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (amplitudeConstant_nonneg _ _ hB) (div_nonneg hτ.le hs.le)) hC
  have hl : WeightedBound U s m (amplitudeConstant n m B * (τ / s) * C)
      (initialMode τ h K hKU V 0 - V) := hv
  have hg := hl.extend_support h.isOpen ((initialMode τ h K hKU V 0 - V).tsupport_subset.trans hKU) hn
  exact supportedSeminorm_le_of_weightedBound hs hn _ hg

lemma initialMode_free_residual (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {B : ℝ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hB : 0 ≤ B)
    (m : ℕ) (hc : FullModeCoefficientBound G U s (m + 1) B)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ p ∈ U, coordDeriv dx G p ⬝ᵥ V p = 0)
    (hY : ∀ p ∈ U, coordDeriv dy G p ⬝ᵥ V p = 0)
    (hV : ∀ p ∈ U, goodSecond G p ⬝ᵥ V p = 0) :
    supportedWeightedSeminorm K s m (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) ≤
      fullErrorConstant n m B * (τ / s) * supportedWeightedSeminorm K s (m + 1) V := by
  let C := supportedWeightedSeminorm K s (m + 1) V
  have hC : 0 ≤ C := apply_nonneg _ _
  have hv := weighted_residual_modeApprox hτ hG h hs hs1 hB hC
    (f := fun _ => 0) contDiffOn_const V.contDiff.contDiffOn hX hY hV 0 m hc
    ((weightedBound_zero U s (m + 1)).mono_const hC)
    ((weightedBound_of_supportedSeminorm s (m + 1) V).restrict_open h.isOpen)
  have hn : 0 ≤ fullErrorConstant n m B * (τ / s) * C :=
    mul_nonneg (mul_nonneg (fullErrorConstant_nonneg _ _ hB) (div_nonneg hτ.le hs.le)) hC
  have hl : WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) := by
    change WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (conjugatedD τ G (initialAmplitude τ G V (fun _ => 0)))
    simp only [Nat.add_zero, zero_add, pow_one, modeApprox] at hv
    change WeightedBound U s m (fullErrorConstant n m B * (τ / s) * C)
      (fun p => conjugatedD τ G (initialAmplitude τ G V (fun _ => 0)) p - (0 : Fin 3 → ℂ)) at hv
    simpa only [sub_zero] using hv
  have hg := hl.extend_support h.isOpen
    ((conjugatedDLM τ hG K (initialMode τ h K hKU V 0)).tsupport_subset.trans hKU) hn
  exact supportedSeminorm_le_of_weightedBound hs hn _ hg

end ClosedSurfaceR4.SmallModes

end

end OAI
