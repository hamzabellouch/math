import OAI.Geometry.SurfaceImmersion.Geometry.SupportedNormalSeed

namespace OAI

/-! Normalization of the actual corrected metric mean by the seed amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

def normalizedPerturbedMean (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) : ℝ :=
  let V := supportedFreeSeed δ τ hF h K hKU b
  let T := perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
  δ⁻¹ ^ 2 * seedMeanError τ T V V v w p

lemma perturbed_seed_mean_identity (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) (hp : p ∈ U) :
    let V := supportedFreeSeed δ τ hF h K hKU b
    let T := perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
    QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T V) w p) =
      δ ^ 2 * (b p ^ 2 * v.1 * w.1 + normalizedPerturbedMean δ τ hF h K hKU R q b v w p) := by
  dsimp only
  rw [corrected_seed_mean δ hτ hF h K hKU b _ v w p hp, normalizedPerturbedMean]
  field_simp [hδ]

/-- The normalized metric mean retains one small factor for every fixed
output order, with a finite explicitly identified input order. -/
theorem normalizedPerturbedMean_bound (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : SupportedField (F := ℝ) K,
      supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) b ≤ A →
      ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * C)
        (normalizedPerturbedMean δ τ hF h K hKU R q b v w) := by
  obtain ⟨C, hC, hm⟩ := perturbedFreeLM_mean_bound τ (contDiff_complexify hF) (h.complexDomain hF)
    K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m
  let r := m + 1 + (q + 1) * (L + 1)
  let S := Real.sqrt 2 * 2 ^ r * A * N
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨C * S ^ 2, mul_nonneg hC (sq_nonneg S), ?_⟩
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
  field_simp [hδ.ne', hτ.ne']

end ClosedSurfaceR4.RealModes

end

end OAI
