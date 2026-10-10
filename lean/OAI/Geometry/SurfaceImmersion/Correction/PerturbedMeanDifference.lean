import OAI.Geometry.SurfaceImmersion.Correction.PerturbedMeanBounds

namespace OAI

/-! The actual metric mean correction has a small finite-loss difference bound. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

theorem perturbedFreeLM_mean_difference (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z) (q m : ℕ) :
    let N := m + 1 + (q + 1) * (L + 1)
    let η := τ / s + ε / τ ^ p
    let T := perturbedFreeLM τ hG h K hKU R q
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V W : SupportedField (F := Ambient n) K),
      FreeCoefficient G U V → FreeCoefficient G U W →
      ∀ a d : ℝ, 0 ≤ a → 0 ≤ d →
      supportedWeightedSeminorm K s N V ≤ a → supportedWeightedSeminorm K s N W ≤ a →
      supportedWeightedSeminorm K s N (V - W) ≤ d →
      ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m (C * a * d * η / τ ^ 2)
        (fun x => seedMeanError τ T V V v w x - seedMeanError τ T W W v w x) := by
  dsimp only
  obtain ⟨C, hC, hcmean⟩ := perturbedFreeLM_mean_bound τ hG h K hKU hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro V W hV hW a d ha hd hVa hWa hDiff v w hv hw
  have hsub : FreeCoefficient G U (V - W : SupportedField (F := Ambient n) K) := hV.sub hW
  have h1 := hcmean (V - W) V hsub hV v w hv hw
  have h2 := hcmean W (V - W) hW hsub v w hv hw
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have h1' := h1.mono_const (show C * supportedWeightedSeminorm K s _ (V - W) *
      supportedWeightedSeminorm K s _ V * (τ / s + ε / τ ^ p) / τ ^ 2 ≤
      C * d * a * (τ / s + ε / τ ^ p) / τ ^ 2 by
    gcongr)
  have h2' := h2.mono_const (show C * supportedWeightedSeminorm K s _ W *
      supportedWeightedSeminorm K s _ (V - W) * (τ / s + ε / τ ^ p) / τ ^ 2 ≤
      C * a * d * (τ / s + ε / τ ^ p) / τ ^ 2 by
    gcongr)
  have hadd := h1'.add isOpen_univ.uniqueDiffOn hs.le
    (seedMeanError_smooth τ _ (V - W) V v w).contDiffOn
    (seedMeanError_smooth τ _ W (V - W) v w).contDiffOn h2'
  have he := hadd.congr (fun x _ => seedMeanError_difference τ _ V W v w x)
  convert he using 1
  ring

end ClosedSurfaceR4.SmallModes

end

end OAI
