import OAI.MeasureTheory.Falconer.Estimates.SliceAverage
import Mathlib.Analysis.Complex.Isometry

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceFrame (θ : ℝ) (p : ℝ × ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr
    (rotation (Circle.exp θ) (Complex.measurableEquivRealProd.symm p.swap))

theorem sourceFrame_eq (θ z r : ℝ) :
    sourceFrame θ (z,r) = z • sourceNormal θ + r • sourceDirection θ := by
  ext i
  fin_cases i <;>
    simp [sourceFrame,sourceNormal,sourceDirection,rotation_apply,Circle.coe_exp,
      Complex.exp_mul_I,Complex.measurableEquivRealProd_symm_apply,
      Complex.orthonormalBasisOneI_repr_apply, -Complex.ofReal_cos,-Complex.ofReal_sin] <;>
    simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,Complex.ofReal_re] <;> ring

@[fun_prop] theorem continuous_sourceFrame (θ : ℝ) : Continuous (sourceFrame θ) := by
  have he : sourceFrame θ = fun p : ℝ × ℝ => p.1 • sourceNormal θ + p.2 • sourceDirection θ := by
    funext p
    exact sourceFrame_eq θ p.1 p.2
  rw [he]
  fun_prop

theorem sourceFrame_measurePreserving (θ : ℝ) :
    MeasurePreserving (sourceFrame θ) volume volume := by
  have h₁ : MeasurePreserving (fun p : ℝ × ℝ => p.swap) volume volume :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p)
      volume volume := Complex.volume_preserving_equiv_real_prod.symm
  have h₃ : MeasurePreserving (fun z : ℂ => rotation (Circle.exp θ) z) volume volume :=
    LinearIsometryEquiv.measurePreserving (rotation (Circle.exp θ))
  have h₄ : MeasurePreserving (fun z : ℂ => Complex.orthonormalBasisOneI.repr z) volume volume :=
    LinearIsometryEquiv.measurePreserving Complex.orthonormalBasisOneI.repr
  exact h₄.comp (h₃.comp (h₂.comp h₁))

theorem sourceProjection_frame (θ z r : ℝ) : sourceProjection θ (sourceFrame θ (z,r)) = z := by
  rw [sourceFrame_eq]
  simp only [sourceProjection,sourceNormal,sourceDirection,PiLp.add_apply,PiLp.smul_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.orthonormalBasisOneI_repr_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,add_zero,zero_add,sub_zero,smul_eq_mul]
  nlinarith [congrArg (fun x : ℝ => z*x) (Real.sin_sq_add_cos_sq θ)]

noncomputable def projectedDensity (a : Plane → ℝ≥0∞) (θ z : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, a (sourceFrame θ (z,r))

@[fun_prop] theorem measurable_projectedDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (θ : ℝ) :
    Measurable (projectedDensity a θ) := by
  exact (ha.comp (continuous_sourceFrame θ).measurable).lintegral_prod_right'

theorem projectedMeasure_withDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (θ : ℝ) :
    projectedMeasure (volume.withDensity a) θ = volume.withDensity (projectedDensity a θ) := by
  have hP : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  ext S hS
  rw [projectedMeasure,Measure.map_apply hP hS,withDensity_apply _ (hS.preimage hP),
    withDensity_apply _ hS]
  have h := (sourceFrame_measurePreserving θ).setLIntegral_comp_preimage (hS.preimage hP) ha
  have hset : sourceFrame θ ⁻¹' (sourceProjection θ ⁻¹' S) = S ×ˢ univ := by
    ext ⟨z,r⟩
    simp only [mem_preimage,sourceProjection_frame,mem_prod,mem_univ,and_true]
  rw [hset] at h
  change (∫⁻ p : ℝ × ℝ in S ×ˢ univ, a (sourceFrame θ p) ∂volume.prod volume) = _ at h
  rw [setLIntegral_prod _ (by fun_prop)] at h
  simpa only [setLIntegral_univ,projectedDensity] using h.symm

noncomputable def sourceAlong (θ : ℝ) (x : Plane) : ℝ :=
  Real.cos θ * x 0 + Real.sin θ * x 1

theorem sourceFrame_inverse (θ : ℝ) (x : Plane) :
    sourceFrame θ (sourceProjection θ x,sourceAlong θ x) = x := by
  rw [sourceFrame_eq]
  ext i
  fin_cases i <;>
    simp [sourceProjection,sourceAlong,sourceNormal,sourceDirection,
      Complex.orthonormalBasisOneI_repr_apply,-Complex.ofReal_cos,-Complex.ofReal_sin] <;>
    nlinarith [congrArg (fun a : ℝ => x 0*a) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun a : ℝ => x 1*a) (Real.sin_sq_add_cos_sq θ)]

theorem sourceFrame_line (θ : ℝ) (x : Plane) (r : ℝ) :
    sourceFrame θ (sourceProjection θ x,r+sourceAlong θ x) = x + r • sourceDirection θ := by
  have hx := sourceFrame_inverse θ x
  rw [sourceFrame_eq] at hx
  rw [sourceFrame_eq,add_smul]
  calc
    _ = (sourceProjection θ x • sourceNormal θ + sourceAlong θ x • sourceDirection θ) +
        r • sourceDirection θ := by abel
    _ = _ := by rw [hx]

theorem projectedDensity_line (a : Plane → ℝ≥0∞) (θ : ℝ) (x : Plane) :
    projectedDensity a θ (sourceProjection θ x) = ∫⁻ r : ℝ, a (x+r • sourceDirection θ) := by
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun r => a (sourceFrame θ (sourceProjection θ x,r))) (sourceAlong θ x)
  simp_rw [sourceFrame_line] at h
  exact h.symm

end PlanarFalconer

end OAI
