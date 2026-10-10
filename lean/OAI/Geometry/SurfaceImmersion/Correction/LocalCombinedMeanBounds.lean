import OAI.Geometry.SurfaceImmersion.Correction.LocalCombinedMean

namespace OAI

/-! Uniform finite-loss value and difference bounds for the actual local
combined mean operator on the positive trial ball. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates FiniteMean
open JetPolynomial (SupportedField supportedWeightedSeminorm weightedBound_comp_isometry)
open JetPolynomial.Perturbation (modeSupport)

variable {n : ℕ} {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

theorem localCombinedMean_estimates (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (d : Budgets U V s F ψ Q χ e) (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ)
    (hKV : (modeSupport K : Set Base) ⊆ V)
    {P : Fin 3 → Fin n → JetPolynomial.Expression} {J : Set JetPolynomial.Base}
    {O Q₀ : Set JetPolynomial.LowJet} (hJ : IsOpen J) (hO : IsOpen O)
    (hQ₀ : IsCompact Q₀) (hQO : Q₀ ⊆ O) (hP : ∀ i l, (P i l).SmoothCoeffs O)
    (hKJ : (K : Set JetPolynomial.Base) ⊆ J)
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGQ : Set.MapsTo (JetPolynomial.lowJet G) J Q₀)
    {L : ℕ} (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m) (q m : ℕ) (C B₀ : ℝ)
    (hB₀ : 1 ≤ B₀)
    (hGb : WeightedBound J s (m + JetPolynomial.Perturbation.tensorOrder P) B₀ (JetPolynomial.lowJet G)) :
    ∃ β κ : ℝ, 1 ≤ β ∧ 1 ≤ κ ∧ ∀ (δ τ ε : ℝ) (p : ℕ),
      0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      JetPolynomial.Perturbation.tensorLoss P ≤ p → τ / s + ε / τ ^ p ≤ 1 →
      ∀ (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
        SupportedField (F := Fin 3 → ℂ) (modeSupport K)),
      (∀ m Z, supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) ⟨s, hs.le⟩ (m + L) Z) →
      ∀ (A B : Base → Tensor) (a : ℝ), 0 ≤ C → 0 ≤ a →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B U →
      InTrialBall U reference r A → InTrialBall U reference r B →
      WeightedBound U s (m + (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1))) C A →
      WeightedBound U s (m + (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1))) C B →
      WeightedBound U s (m + (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1))) a (A - B) →
      WeightedBound U s m ((τ / s + ε / τ ^ p) * β)
        (localCombinedMean h hρ hKV P G δ τ ε R q A) ∧
      WeightedBound U s m (κ * (τ / s + ε / τ ^ p) * a)
        (localCombinedMean h hρ hKV P G δ τ ε R q A -
          localCombinedMean h hρ hKV P G δ τ ε R q B) := by
  let N := m + JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1)
  obtain ⟨A₀, hA₀, ha⟩ := supportedTrialAmplitude_bounds h d hs hs1 hρ hKV N C
  obtain ⟨E, hE, he⟩ := JetPolynomial.Perturbation.combinedSeedTensor_bounds
    (L := L) hJ hO hQ₀ hQO P hP m B₀ hB₀ h.smoothF h.domain K hKJ hKV
    (fun j => d.mode (j + 1)) D (fun j => zero_le_one.trans (d.mode_pos _)) hD
    q A₀ (d.normal N) (zero_le_one.trans hA₀) (zero_le_one.trans (d.normal_pos N))
  let β := max 1 (outputFactor d m * E)
  let κ := max 1 (outputFactor d m * (2 * E * inputFactor d N))
  refine ⟨β, κ, le_max_left _ _, le_max_left _ _, ?_⟩
  intro δ τ ε p hδ hτ hτs hε hε1 hp hsmall R hR A B a hC ha0 hA hB hballA hballB hbA hbB hab
  have hN : m + (JetPolynomial.Perturbation.tensorOrder P + 1 + (q + 1) * (L + 1)) = N := by
    dsimp only [N]
    omega
  rw [hN] at hbA hbB hab
  obtain ⟨habA, habB, habD⟩ := ha A B a hC ha0 hA hB hballA hballB hbA hbB hab
  have hh := he G hG ⟨s, hs.le⟩ δ τ ε p hδ hτ hs hτs hs1 hε hε1 hp hsmall hGQ hGb
    (fun j => d.mode_bound (j + 1)) R hR (d.normal_bound N)
    (supportedTrialAmplitude h hρ hKV A) (supportedTrialAmplitude h hρ hKV B)
    (inputFactor d N * a) (mul_nonneg (inputFactor_nonneg d N) ha0) habA habB
    (by simpa only [mul_assoc] using habD)
  have hsA := JetPolynomial.Perturbation.combinedMeanTensor_smooth hJ hO hP δ τ ε hG
    (fun _ hx => hQO (hGQ hx)) h.smoothF h.domain K hKJ hKV R q (supportedTrialAmplitude h hρ hKV A)
  have hsB := JetPolynomial.Perturbation.combinedMeanTensor_smooth hJ hO hP δ τ ε hG
    (fun _ hx => hQO (hGQ hx)) h.smoothF h.domain K hKJ hKV R q (supportedTrialAmplitude h hρ hKV B)
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hva := weightedBound_comp_isometry JetPolynomial.planeCoordinateIsometry.symm hsA hh.1
  have hda := weightedBound_comp_isometry JetPolynomial.planeCoordinateIsometry.symm (hsA.sub hsB) hh.2
  have htv := h.transport_bound d hs hs1 (mul_nonneg hη hE)
    (hsA.comp JetPolynomial.planeCoordinateIsometry.symm.contDiff).contDiffOn
    (hva.restrict_open h.domain.isOpen)
  have hi := inputFactor_nonneg d N
  have htd := h.transport_bound d hs hs1 (by positivity)
    ((hsA.sub hsB).comp JetPolynomial.planeCoordinateIsometry.symm.contDiff).contDiffOn
    (hda.restrict_open h.domain.isOpen)
  constructor
  · apply htv.mono_const
    calc
      outputFactor d m * ((τ / s + ε / τ ^ p) * E) = (τ / s + ε / τ ^ p) * (outputFactor d m * E) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hη
  · have hc : outputFactor d m * ((τ / s + ε / τ ^ p) * (2 * E) * (inputFactor d N * a)) ≤
        κ * (τ / s + ε / τ ^ p) * a := by
      calc
        _ = (outputFactor d m * (2 * E * inputFactor d N)) * ((τ / s + ε / τ ^ p) * a) := by ring
        _ ≤ κ * ((τ / s + ε / τ ^ p) * a) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hη ha0)
        _ = _ := by ring
    apply (htd.mono_const hc).congr
    intro x hx
    exact (map_sub (pullbackField χ x) _ _).symm

end ClosedSurfaceR4.PhaseMean

end

end OAI
