import OAI.Analysis.KadisonKastler.ResolventCyclicModel
import OAI.Analysis.KadisonKastler.RegularCoreFields

namespace OAI

/-! # Multipliers in the cyclic spectral model -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventScalarMultiplier (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C) :
    ResolventCyclicL2 R hR x →L[ℂ] ResolventCyclicL2 R hR x :=
  regularFieldOperator (resolventVectorMeasure R hR x) (fun s => φ s • (1 : ℂ →L[ℂ] ℂ))
    (fun z => hφ.aestronglyMeasurable.smul_const z) C
    (Eventually.of_forall fun s => by
      apply le_trans _ (hC s)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl)

theorem resolventScalarMultiplier_apply_ae (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C)
    (v : ResolventCyclicL2 R hR x) :
    resolventScalarMultiplier R hR x φ hφ C hC v =ᵐ[resolventVectorMeasure R hR x]
      fun s => φ s * v s := by
  have h := regularFieldOperator_represents (resolventVectorMeasure R hR x)
    (fun s => φ s • (1 : ℂ →L[ℂ] ℂ))
    (fun z => hφ.aestronglyMeasurable.smul_const z) C
    (Eventually.of_forall fun s => by
      apply le_trans _ (hC s)
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      simp only [smul_apply, one_apply_eq_self, norm_smul]
      exact le_rfl) v
  simpa only [resolventScalarMultiplier, smul_apply, one_apply_eq_self, smul_eq_mul] using h

theorem resolventScalarMultiplier_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (g f : C(spectrum ℝ R, ℂ)) :
    resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm
      (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f) =
    ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ (g * f) := by
  apply Lp.ext
  filter_upwards [resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖
    g.norm_coe_le_norm (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (resolventVectorMeasure R hR x) f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (resolventVectorMeasure R hR x) (g * f)] with s hs hf hgf
  rw [hs, hf, hgf]
  rfl

theorem resolventCyclicIsometry_multiplier (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (g : C(spectrum ℝ R, ℂ)) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm v) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) := by
  have hd := ContinuousMap.toLp_denseRange ℂ (p := 2) (resolventVectorMeasure R hR x) ℂ
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  refine hd.induction_on (p := fun w : ResolventCyclicL2 R hR x =>
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x w)) v ?_ ?_
  · exact isClosed_eq
      ((resolventCyclicIsometry R hR x).continuous.comp
        (resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm).continuous)
      ((resolventContinuousCalculus R hR g).continuous.comp
        (resolventCyclicIsometry R hR x).continuous)
  · intro f
    rw [resolventScalarMultiplier_continuous, resolventCyclicIsometry_continuous,
      resolventCyclicIsometry_continuous, map_mul, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
