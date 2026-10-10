import OAI.Geometry.SurfaceImmersion.Correction.UniformMetricMeanDifference
import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedPerturbedDifference

namespace OAI

/-! Explicit constants for the normalized geometric metric mean, independent
of its oscillation and amplitude scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

def normalizedMeanBudget (L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) (N : ℝ) : ℝ :=
  freeMeanBudget 4 L B D q m *
    (Real.sqrt 2 * 2 ^ (m + 1 + (q + 1) * (L + 1)) * N) ^ 2

lemma normalizedMeanBudget_nonneg (L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) (N : ℝ) :
    0 ≤ normalizedMeanBudget L B D q m N :=
  mul_nonneg (freeMeanBudget_nonneg 4 L B D hB q m) (sq_nonneg _)

theorem normalizedMeanBudget_bound (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + 1) (B m))
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hbN : WeightedBound U s (m + 1 + (q + 1) * (L + 1)) N (freeNormal F)) :
    ∀ b : SupportedField (F := ℝ) K,
      supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) b ≤ A →
      ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * (normalizedMeanBudget L B D q m N * A ^ 2))
        (normalizedPerturbedMean δ τ hF h K hKU R q b v w) := by
  let C := freeMeanBudget 4 L B D q m
  have hC : 0 ≤ C := freeMeanBudget_nonneg 4 L B D hB q m
  have hm := freeMeanBudget_bound τ (contDiff_complexify hF) (h.complexDomain hF)
    K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m
  let r := m + 1 + (q + 1) * (L + 1)
  let S := Real.sqrt 2 * 2 ^ r * A * N
  have hS : 0 ≤ S := by dsimp [S]; positivity
  intro b hb v w hv hw
  let V := supportedFreeSeed δ τ hF h K hKU b
  have hV := supportedFreeSeed_isFree δ τ hF h K hKU b
  have hn := supportedFreeSeed_bound hF h K hKU b hδ.le hτ.le hs hA hN r hb hbN
  have hh := hm V V hV hV v w hv hw
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hh' := hh.mono_const (show C * supportedWeightedSeminorm K s r V *
      supportedWeightedSeminorm K s r V * (τ / s + ε / τ ^ p) / τ ^ 2 ≤
      C * (S * (δ * τ)) * (S * (δ * τ)) * (τ / s + ε / τ ^ p) / τ ^ 2 by
    gcongr)
  have hsm := seedMeanError_smooth τ
    (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q) V V v w
  have hscaled := hh'.const_smul isOpen_univ.uniqueDiffOn hsm.contDiffOn (δ⁻¹ ^ 2)
  change WeightedBound Set.univ s m _ (normalizedPerturbedMean δ τ hF h K hKU R q b v w) at hscaled
  convert hscaled using 1
  rw [abs_of_nonneg (sq_nonneg δ⁻¹)]
  dsimp [normalizedMeanBudget, C, S, r]
  field_simp [hδ.ne', hτ.ne']


theorem normalizedMeanBudget_difference (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + 1) (B m))
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hbN : WeightedBound U s (m + 1 + (q + 1) * (L + 1)) N (freeNormal F)) :
    ∀ (b c : SupportedField (F := ℝ) K) (d : ℝ), 0 ≤ d →
      supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) b ≤ A →
      supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) c ≤ A →
      supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) (b - c) ≤ d →
      ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m (2 * normalizedMeanBudget L B D q m N * A * (τ / s + ε / τ ^ p) * d)
        (fun x => normalizedPerturbedMean δ τ hF h K hKU R q b v w x -
          normalizedPerturbedMean δ τ hF h K hKU R q c v w x) := by
  let C := 2 * freeMeanBudget 4 L B D q m
  have hm := freeMeanBudget_difference τ (contDiff_complexify hF) (h.complexDomain hF)
    K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m
  let r := m + 1 + (q + 1) * (L + 1)
  let S := Real.sqrt 2 * 2 ^ r * N
  have hS : 0 ≤ S := by dsimp [S]; positivity
  intro b c d hd hb hc' hbc v w hv hw
  let V := supportedFreeSeed δ τ hF h K hKU b
  let W := supportedFreeSeed δ τ hF h K hKU c
  have hV := supportedFreeSeed_isFree δ τ hF h K hKU b
  have hW := supportedFreeSeed_isFree δ τ hF h K hKU c
  have hvn := supportedFreeSeed_bound hF h K hKU b hδ.le hτ.le hs hA hN r hb hbN
  have hwn := supportedFreeSeed_bound hF h K hKU c hδ.le hτ.le hs hA hN r hc' hbN
  have hdn := supportedFreeSeed_bound hF h K hKU (b - c) hδ.le hτ.le hs hd hN r hbc hbN
  rw [supportedFreeSeed_sub] at hdn
  have hva : supportedWeightedSeminorm K s r V ≤ S * A * (δ * τ) := by
    convert hvn using 1
    dsimp [S]
    ring
  have hwa : supportedWeightedSeminorm K s r W ≤ S * A * (δ * τ) := by
    convert hwn using 1
    dsimp [S]
    ring
  have hda : supportedWeightedSeminorm K s r (V - W) ≤ S * d * (δ * τ) := by
    convert hdn using 1
    dsimp [S]
    ring
  have hh := hm V W hV hW (S * A * (δ * τ)) (S * d * (δ * τ))
    (by positivity) (by positivity) hva hwa hda v w hv hw
  let T := perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
  have hsm := (seedMeanError_smooth τ T V V v w).sub (seedMeanError_smooth τ T W W v w)
  have hh' := hh.const_smul isOpen_univ.uniqueDiffOn hsm.contDiffOn (δ⁻¹ ^ 2)
  have hcongr := hh'.congr (fun x _ => show
      normalizedPerturbedMean δ τ hF h K hKU R q b v w x -
        normalizedPerturbedMean δ τ hF h K hKU R q c v w x =
      δ⁻¹ ^ 2 • (seedMeanError τ T V V v w x - seedMeanError τ T W W v w x) by
    change δ⁻¹ ^ 2 * _ - δ⁻¹ ^ 2 * _ = δ⁻¹ ^ 2 * (_ - _)
    ring)
  convert hcongr using 1
  rw [abs_of_nonneg (sq_nonneg δ⁻¹)]
  dsimp [normalizedMeanBudget, C, S, r]
  field_simp [hδ.ne', hτ.ne']

end ClosedSurfaceR4.RealModes

end

end OAI
