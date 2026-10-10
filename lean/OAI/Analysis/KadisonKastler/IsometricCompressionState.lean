import OAI.Analysis.KadisonKastler.HilbertCompression
import OAI.Analysis.KadisonKastler.PureStateExtension

namespace OAI

/-! # States pulled back through an isometric compression -/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def operatorCompression (V : H →L[ℂ] K) :
    (K →L[ℂ] K) →L[ℂ] (H →L[ℂ] H) :=
  (hilbertCompression V).mkContinuous (‖V‖^2) (fun T => by
    change ‖V.adjoint.comp (T.comp V)‖ ≤ ‖V‖^2*‖T‖
    calc
      _ ≤ ‖V.adjoint‖*(‖T‖*‖V‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring)

@[simp] theorem operatorCompression_apply (V : H →L[ℂ] K) (T : K →L[ℂ] K) :
    operatorCompression V T=V.adjoint.comp (T.comp V) := rfl

theorem state_comp_isometricCompression
    (V : H →L[ℂ] K) (hV : Isometry V)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (φ.comp (operatorCompression V)) := by
  apply (isState_iff _).mpr
  constructor
  · change φ (V.adjoint.comp V)=1
    rw [V.isometry_iff_adjoint_comp_self.mp hV]
    exact ((isState_iff φ).mp hφ).1
  · intro T
    have he : operatorCompression V (star T*T)=(T.comp V).adjoint.comp (T.comp V) := by
      simp only [operatorCompression_apply,ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.star_eq_adjoint]
      rfl
    change (φ (operatorCompression V (star T*T))).im=0 ∧
      0 ≤ (φ (operatorCompression V (star T*T))).re
    rw [he]
    have hp := (positiveOfSquares φ hφ.2).map_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (ContinuousLinearMap.isPositive_adjoint_comp_self (T.comp V)))
    exact ⟨hp.2.symm,hp.1⟩

end

end KadisonKastler

end OAI
