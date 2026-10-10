import OAI.Analysis.KadisonKastler.ResolventCyclicMultipliers

namespace OAI

/-! # The resolvent coordinate in its scalar cyclic model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCoordinateFunction (R : H →L[ℂ] H) : C(spectrum ℝ R, ℂ) :=
  ⟨fun s => (s.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def resolventCoordinateOperator (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    ResolventCyclicL2 R hR x →L[ℂ] ResolventCyclicL2 R hR x :=
  resolventScalarMultiplier R hR x (resolventCoordinateFunction R)
    (resolventCoordinateFunction R).continuous.measurable
    ‖resolventCoordinateFunction R‖ (resolventCoordinateFunction R).norm_coe_le_norm

theorem resolventCoordinateOperator_apply_ae (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCoordinateOperator R hR x v =ᵐ[resolventVectorMeasure R hR x]
      fun s => (s.val : ℂ) * v s :=
  resolventScalarMultiplier_apply_ae R hR x (resolventCoordinateFunction R)
    (resolventCoordinateFunction R).continuous.measurable
    ‖resolventCoordinateFunction R‖ (resolventCoordinateFunction R).norm_coe_le_norm v

theorem resolventCoordinateOperator_intertwines (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x (resolventCoordinateOperator R hR x v) =
      R (resolventCyclicIsometry R hR x v) := by
  have hc : resolventContinuousCalculus R hR (resolventCoordinateFunction R) = R :=
    (resolventContinuousCalculus_ofReal R hR
      ((ContinuousMap.id ℝ).restrict (spectrum ℝ R))).trans (cfcHom_id hR)
  exact (resolventCyclicIsometry_multiplier R hR x (resolventCoordinateFunction R) v).trans
    (congrArg (fun T : H →L[ℂ] H => T (resolventCyclicIsometry R hR x v)) hc)

theorem one_sub_resolventCoordinateOperator_intertwines (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    resolventCyclicIsometry R hR x ((1 - resolventCoordinateOperator R hR x) v) =
      (1 - R) (resolventCyclicIsometry R hR x v) := by
  simp only [sub_apply, one_apply_eq_self, map_sub, resolventCoordinateOperator_intertwines]

end

end KadisonKastler

end OAI
