import OAI.Analysis.KadisonKastler.ModularCyclicGroup
import OAI.Analysis.KadisonKastler.ResolventCyclicCuts
import OAI.Analysis.KadisonKastler.ResolventCutMeasurable
import OAI.Analysis.KadisonKastler.CharacterContinuity

namespace OAI

/-! # Measurable modular cut fields in the cyclic coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem lt_modularCutThreshold_iff {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (a : ℝ) :
    s < modularCutThreshold a ↔ a < resolventLogFrequency s := by
  unfold modularCutThreshold resolventLogFrequency
  rw [lt_sub_iff_add_lt, Real.lt_log_iff_exp_lt (sub_pos.mpr hs1), Real.exp_add, Real.exp_log hs]
  have hp : 0 < 1 + Real.exp a := by positivity
  rw [show (1 + Real.exp a)⁻¹ = (1 + Real.exp a)⁻¹ * 1 by rw [mul_one], lt_inv_mul_iff₀ hp]
  constructor <;> intro h <;> nlinarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def modularCyclicCut (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ) :
    ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x :=
  resolventScalarMultiplier _ _ x
    (resolventCutIndicator (graphResolvent M J Ω 1) (modularCutThreshold a))
    (resolventCutIndicator_measurable _ _) 1 (resolventCutIndicator_bound _ _)

theorem modularCyclicCut_intertwines (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ)
    (v : ModularCyclicSpace M J Ω x) :
    resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x
      (modularCyclicCut M J Ω x a v) =
    modularUpperCut M J Ω a
      (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v) :=
  resolventCyclicIsometry_cut _ _ x _ v

theorem modularCyclicCut_contracts (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ) :
    ‖modularCyclicCut M J Ω x a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, ← (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).norm_map,
    modularCyclicCut_intertwines]
  calc
    _ ≤ ‖modularUpperCut M J Ω a‖ *
        ‖resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v‖ :=
      (modularUpperCut M J Ω a).le_opNorm _
    _ ≤ 1 * ‖resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x v‖ :=
      mul_le_mul_of_nonneg_right (modularUpperCut_contracts (M := M) J Ω a) (norm_nonneg _)
    _ = ‖v‖ := by rw [one_mul, LinearIsometry.norm_map]

variable [TopologicalSpace.SeparableSpace H]

theorem modularCyclicCut_measurable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω x : H) (a : ℝ)
    (v : ModularCyclicSpace M J Ω x) :
    AEStronglyMeasurable (fun ξ : ℝ => modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ) v) volume := by
  apply (resolventCyclicIsometry _ (graphResolvent_positive J Ω 1).isSelfAdjoint x).isometry.isEmbedding.aestronglyMeasurable_comp_iff.mp
  simp_rw [modularCyclicCut_intertwines]
  exact modularUpperCut_measurable J Ω a _

end

end KadisonKastler

end OAI
