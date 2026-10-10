import OAI.Geometry.SurfaceImmersion.Correction.UniformFreeModeConstants
import OAI.Geometry.SurfaceImmersion.Correction.SupportedMeanError
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledGradientEstimates

namespace OAI

/-! The metric mean budget is fixed before either scale is selected. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

def freeMeanBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  let A := freeModeBudget n L B D q (m + 1)
  (n : ℝ) * 2 ^ m * ((1 + 2 * A) * (2 + 2 * A) + (1 + 2 * A))

lemma freeMeanBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeMeanBudget n L B D q m := by
  have hA := freeModeBudget_nonneg n L B D hB q (m + 1)
  unfold freeMeanBudget
  positivity

theorem freeMeanBudget_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
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
    ∀ (V W : SupportedField (F := Ambient n) K),
      FreeCoefficient G U V → FreeCoefficient G U W →
      ∀ v w : Base, ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      WeightedBound Set.univ s m
        (freeMeanBudget n L B D q m * supportedWeightedSeminorm K s N V * supportedWeightedSeminorm K s N W * η / τ ^ 2)
        (seedMeanError τ T V W v w) := by
  dsimp only
  let A := freeModeBudget n L B D q (m + 1)
  have hA : 0 ≤ A := freeModeBudget_nonneg n L B D hB q (m + 1)
  let η := τ / s + ε / τ ^ p
  let N := m + 1 + (q + 1) * (L + 1)
  let T := perturbedFreeLM τ hG h K hKU R q
  have hη : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hratio : τ / s ≤ η := le_add_of_nonneg_right (div_nonneg hε (pow_nonneg hτ.le _))
  have hw (V : SupportedField (F := Ambient n) K) (hV : FreeCoefficient G U V) :
      WeightedBound Set.univ s (m + 1) ((1 + A) * supportedWeightedSeminorm K s N V) (T V) ∧
      WeightedBound Set.univ s m (η * (A * supportedWeightedSeminorm K s N V)) (fun x => T V x - V x) ∧
      WeightedBound Set.univ s m (supportedWeightedSeminorm K s N V) V := by
    have he := freeModeBudget_bound hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q (m + 1) V hV
    have hz := freeModeBudget_size hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q (m + 1) V hV
    refine ⟨(weightedBound_of_supportedSeminorm s (m + 1) (T V)).mono_const hz, ?_, ?_⟩
    · have he' := ((weightedBound_of_supportedSeminorm s (m + 1) (T V - V)).mono_const he).mono_order
        (show m ≤ m + 1 by omega)
      convert he' using 1
      ring
    · exact (weightedBound_of_supportedSeminorm s N V).mono_order (by dsimp [N]; omega)
  intro V W hV hW v w hv hw'
  obtain ⟨hZ, hE, hVb⟩ := hw V hV
  obtain ⟨hZ', hE', hWb⟩ := hw W hW
  have hVN : 0 ≤ supportedWeightedSeminorm K s N V := apply_nonneg _ _
  have hWN : 0 ≤ supportedWeightedSeminorm K s N W := apply_nonneg _ _
  have hm := weighted_mean_small_error isOpen_univ hτ hs hη hsmall hratio
    (mul_nonneg (by linarith : 0 ≤ 1 + A) hVN) (mul_nonneg hA hVN) hVN
    (mul_nonneg (by linarith : 0 ≤ 1 + A) hWN) (mul_nonneg hA hWN) hWN
    (T V).contDiff.contDiffOn V.contDiff.contDiffOn (T W).contDiff.contDiffOn W.contDiff.contDiffOn
    hZ hE hVb hZ' hE' hWb v w hv hw'
  change WeightedBound Set.univ s m _ (seedMeanError τ T V W v w) at hm
  convert hm using 1
  dsimp [freeMeanBudget, A]
  ring

end ClosedSurfaceR4.SmallModes

end

end OAI
