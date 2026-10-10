import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPeriodMeasure

namespace OAI

/-! The literal half-open level-three cell is a fundamental domain for
horizontal translations. This is the measure bridge for Hecke constant modes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def CubicThetaPeriodGroup := Multiplicative Eisenstein

instance : CommGroup CubicThetaPeriodGroup := inferInstanceAs (CommGroup (Multiplicative Eisenstein))
instance : Countable CubicThetaPeriodGroup := by
  change Countable Eisenstein
  exact coordinatesEquiv.symm.injective.countable

instance cubicThetaPeriodGroup_action : MulAction CubicThetaPeriodGroup ℂ where
  smul g z := z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
  one_smul z := by change z+3*((0:Eisenstein):ℂ)=z; simp
  mul_smul g h z := by
    change z+3*((Multiplicative.toAdd g+Multiplicative.toAdd h:Eisenstein):ℂ)=
      (z+3*((Multiplicative.toAdd h:Eisenstein):ℂ))+3*((Multiplicative.toAdd g:Eisenstein):ℂ)
    push_cast
    ring

instance cubicThetaPeriodGroup_continuous : ContinuousConstSMul CubicThetaPeriodGroup ℂ where
  continuous_const_smul g := by
    change Continuous (fun z : ℂ => z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))
    fun_prop

instance cubicThetaPeriodGroup_measure : SMulInvariantMeasure CubicThetaPeriodGroup ℂ volume where
  measure_preimage_smul g A _ := by
    change volume ((fun z : ℂ => z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)) ⁻¹' A)=volume A
    exact measure_preimage_add_right volume _ A

theorem cubicThetaHorizontalCell_unique (z : ℂ) :
    ∃! g : CubicThetaPeriodGroup,g • z∈cubicThetaHorizontalCell := by
  let x := cubicThetaPeriodCoordinates z
  let n : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let w := coordinatesEquiv n
  refine ⟨Multiplicative.ofAdd w,?_,?_⟩
  · intro i
    change cubicThetaPeriodCoordinates (z+3*(w:ℂ)) i∈Ico (0:ℝ) 1
    rw [cubicThetaPeriodCoordinates_translate]
    have he : (cubicThetaPeriodCoordinates z+fun j => ((coordinatesEquiv.symm w) j:ℝ)) i=
        Int.fract (x i) := by
      simp only [w,LinearEquiv.symm_apply_apply,Pi.add_apply,n,Int.cast_neg]
      rfl
    rw [he]
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  · intro g hg
    change Multiplicative.toAdd g=w
    apply coordinatesEquiv.symm.injective
    funext i
    have hi := hg i
    change cubicThetaPeriodCoordinates (z+3*((Multiplicative.toAdd g:Eisenstein):ℂ)) i∈Ico (0:ℝ) 1 at hi
    rw [cubicThetaPeriodCoordinates_translate] at hi
    have hz : Int.floor ((cubicThetaPeriodCoordinates z) i+
        ((coordinatesEquiv.symm (Multiplicative.toAdd g)) i:ℝ))=0 :=
      Int.floor_eq_zero_iff.mpr hi
    rw [Int.floor_add_intCast] at hz
    change (coordinatesEquiv.symm (Multiplicative.toAdd g)) i=(coordinatesEquiv.symm (coordinatesEquiv n)) i
    rw [LinearEquiv.symm_apply_apply]
    dsimp [n,x]
    omega

theorem cubicThetaHorizontalCell_fundamental (μ : Measure ℂ) :
    IsFundamentalDomain CubicThetaPeriodGroup cubicThetaHorizontalCell μ :=
  IsFundamentalDomain.mk' cubicThetaHorizontalCell_measurable.nullMeasurableSet
    cubicThetaHorizontalCell_unique

end CubicFirstMoment

end

end OAI
