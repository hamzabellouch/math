import OAI.Geometry.SurfaceImmersion.Geometry.SupportedRootAmplitude
import OAI.Geometry.SurfaceImmersion.Correction.UniformNormalizedMean

namespace OAI

/-! Uniform constants for actual square-root trials are chosen before the scales
and the supported perturbation operator. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates RootMean
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

theorem uniform_perturbed_root_mean_bounds (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {p L : ℕ}
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (q m : ℕ) {r R₀ C P N : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (δ τ : ℝ) (s : ℝ≥0) (ε : ℝ),
      0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ p ≤ 1 →
      (∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + 1) (B m)) →
      ∀ (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K),
      (∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
        ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z) →
      WeightedBound U s (m + 1 + (q + 1) * (L + 1)) N (freeNormal F) →
      ∀ (ψ : SupportedField (F := ℝ) K)
      (u v : Base → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
      (hru : Set.MapsTo u U (Set.Icc r R₀)) (hrv : Set.MapsTo v U (Set.Icc r R₀)) (d : ℝ),
      0 ≤ d → supportedWeightedSeminorm K s (m + 1 + (q + 1) * (L + 1)) ψ ≤ P →
      WeightedBound U s (m + 1 + (q + 1) * (L + 1)) C u →
      WeightedBound U s (m + 1 + (q + 1) * (L + 1)) C v →
      WeightedBound U s (m + 1 + (q + 1) * (L + 1)) d (fun x => u x - v x) →
      let bu := supportedRootAmplitude h.isOpen K hKU ψ u hu (fun _ hx => hr.trans_le (hru hx).1)
      let bv := supportedRootAmplitude h.isOpen K hKU ψ v hv (fun _ hx => hr.trans_le (hrv hx).1)
      ∀ a b : Base, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ p) * E)
        (normalizedPerturbedMean δ τ hF h K hKU R q bu a b) ∧
      WeightedBound Set.univ s m (E * (τ / s + ε / τ ^ p) * d)
        (fun x => normalizedPerturbedMean δ τ hF h K hKU R q bu a b x -
          normalizedPerturbedMean δ τ hF h K hKU R q bv a b x) := by
  obtain ⟨A, hA, ha⟩ := supportedRootAmplitude_bounds h.isOpen K hKU (R := R₀) hr hC hP
    (m + 1 + (q + 1) * (L + 1))
  have hA0 := zero_le_one.trans hA
  let Cv := normalizedMeanBudget L B D q m N * A ^ 2
  let Cd := 2 * normalizedMeanBudget L B D q m N * A
  let E := max 1 (max Cv (Cd * A))
  have hvE : Cv ≤ E := (le_max_left _ _).trans (le_max_right _ _)
  have hdE : Cd * A ≤ E := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨E, le_max_left _ _, ?_⟩
  intro δ τ s ε hδ hτ hs hτs hs1 hε hsmall hc R hR hbN
  have hval := normalizedMeanBudget_bound δ τ hF h K hKU hδ hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m A N hA0 hN hbN
  have hdiff := normalizedMeanBudget_difference δ τ hF h K hKU hδ hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m A N hA0 hN hbN
  intro ψ u v hu hv hru hrv d hd hψ hbu hbv hdu
  obtain ⟨hbu', hbv', hdu'⟩ := ha s ψ u v hu hv hru hrv d hs hd hψ hbu hbv hdu
  dsimp only
  intro a b ha hb
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  constructor
  · exact (hval _ hbu' a b ha hb).mono_const (mul_le_mul_of_nonneg_left hvE hη)
  · have hh := hdiff _ _ (A * d) (mul_nonneg hA0 hd) hbu' hbv' hdu' a b ha hb
    apply hh.mono_const
    calc
      Cd * (τ / s + ε / τ ^ p) * (A * d) = (Cd * A) * ((τ / s + ε / τ ^ p) * d) := by ring
      _ ≤ E * ((τ / s + ε / τ ^ p) * d) := mul_le_mul_of_nonneg_right hdE (mul_nonneg hη hd)
      _ = _ := by ring

end ClosedSurfaceR4.RealModes

end

end OAI
