import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTorusModes

namespace OAI

/-! The exact Jacobian of the level-three period cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPeriodEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  eisensteinRealCoords.trans (complexMulEquiv 3 (by norm_num))

lemma cubicThetaPeriodEquiv_apply (x : Fin 2 → ℝ) :
    cubicThetaPeriodEquiv x=cubicThetaPeriodCell x := rfl

lemma cubicThetaPeriodCoordinates_cell (x : Fin 2 → ℝ) :
    cubicThetaPeriodCoordinates (cubicThetaPeriodCell x)=x := by
  unfold cubicThetaPeriodCoordinates cubicThetaPeriodCell
  rw [mul_div_cancel_left₀ _ (by norm_num : (3:ℂ)≠0),ContinuousLinearEquiv.symm_apply_apply]

lemma cubicThetaPeriodEquiv_map_volume :
    Measure.map cubicThetaPeriodEquiv volume=
      ENNReal.ofReal (2/(9*Real.sqrt 3)) • (volume : Measure ℂ) := by
  have he : (cubicThetaPeriodEquiv : (Fin 2 → ℝ) → ℂ)=
      (fun z : ℂ => 3*z) ∘ eisensteinRealCoords := rfl
  rw [he,← Measure.map_map (by fun_prop) eisensteinRealCoords.continuous.measurable,
    eisensteinRealCoords_map_volume,
    Measure.map_smul _ (by fun_prop),complexMul_map_volume 3 (by norm_num),smul_smul]
  congr 1
  norm_num only [Complex.normSq_ofNat,ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma cubicThetaPeriodEquiv_preimage_cell :
    cubicThetaPeriodEquiv ⁻¹' cubicThetaHorizontalCell=
      {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1} := by
  ext x
  simp only [mem_preimage,cubicThetaHorizontalCell,mem_ofPred_eq,cubicThetaPeriodEquiv_apply,
    cubicThetaPeriodCoordinates_cell]

lemma cubicThetaHorizontalCell_integral (f : ℂ → ℂ) :
    (∫ z in cubicThetaHorizontalCell, f z)=
      (9*Real.sqrt 3/2:ℝ) •
        ∫ x in {x : Fin 2 → ℝ | ∀ i, x i∈Ico (0:ℝ) 1}, f (cubicThetaPeriodCell x) := by
  have hi := setIntegral_map_equiv (μ:=volume) cubicThetaPeriodEquiv.toHomeomorph.toMeasurableEquiv f
    cubicThetaHorizontalCell
  change (∫ z in cubicThetaHorizontalCell, f z ∂Measure.map cubicThetaPeriodEquiv volume)=
    ∫ x in cubicThetaPeriodEquiv ⁻¹' cubicThetaHorizontalCell, f (cubicThetaPeriodEquiv x) at hi
  rw [cubicThetaPeriodEquiv_map_volume,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(9*Real.sqrt 3)),
    cubicThetaPeriodEquiv_preimage_cell] at hi
  have he : (9*Real.sqrt 3/2:ℝ)*(2/(9*Real.sqrt 3))=1 := by
    field_simp
  calc
    _ = (9*Real.sqrt 3/2:ℝ) • ((2/(9*Real.sqrt 3):ℝ) •
        ∫ z in cubicThetaHorizontalCell, f z) := by rw [smul_smul,he,one_smul]
    _ = _ := congrArg (fun w : ℂ => (9*Real.sqrt 3/2:ℝ) • w) hi

end CubicFirstMoment

end

end OAI
