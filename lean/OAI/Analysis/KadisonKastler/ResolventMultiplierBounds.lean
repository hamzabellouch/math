import OAI.Analysis.KadisonKastler.ResolventCyclicMultipliers

namespace OAI

/-! # Independence from the chosen scalar multiplier bound -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventScalarMultiplier_bound_independent (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (x : H) (φ : spectrum ℝ R → ℂ) (hφ : Measurable φ)
    (C D : ℝ) (hC : ∀ s, ‖φ s‖ ≤ C) (hD : ∀ s, ‖φ s‖ ≤ D) :
    resolventScalarMultiplier R hR x φ hφ C hC =
      resolventScalarMultiplier R hR x φ hφ D hD := by
  apply ContinuousLinearMap.ext
  intro v
  apply MeasureTheory.Lp.ext
  filter_upwards [resolventScalarMultiplier_apply_ae R hR x φ hφ C hC v,
    resolventScalarMultiplier_apply_ae R hR x φ hφ D hD v] with s hC hD
  rw [hC, hD]

theorem resolventCyclicIsometry_multiplier_of_bound (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (g : C(spectrum ℝ R, ℂ)) (C : ℝ) (hC : ∀ s, ‖g s‖ ≤ C)
    (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x
      (resolventScalarMultiplier R hR x g g.continuous.measurable C hC v) =
    resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x v) := by
  rw [resolventScalarMultiplier_bound_independent R hR x g g.continuous.measurable
    C ‖g‖ hC g.norm_coe_le_norm]
  exact resolventCyclicIsometry_multiplier R hR x g v

end

end KadisonKastler

end OAI
