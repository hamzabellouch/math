import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspVerticalEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoffBounds

namespace OAI

/-! With any prescribed loss above the sharp coefficient one, cutting
off a cusp costs only mass in its fixed compact transition annulus. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspRaw_differentiableAt (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests)
    (z : ℂ) {v : ℝ} (hv : 0<v) :
    DifferentiableAt ℝ (fun t : ℝ => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))) v := by
  have hm := (cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ) (p:=(z,v)) hv).differentiableAt
    (by simp)
  have hp := cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv
  have hf := cubicThetaSectionFunction_differentiable F hp
  have hline : DifferentiableAt ℝ (fun t : ℝ => (z,t)) v :=
    ((hasDerivAt_const v z).prodMk (hasDerivAt_id v)).differentiableAt
  exact DifferentiableAt.comp (g:=cubicThetaSectionFunction F)
    (f:=fun t : ℝ => cubicThetaMobius (cubicThetaFullComplex δ) (z,t)) v hf (hm.comp v hline)

theorem cubicThetaCuspCutoff_energy {ε : ℝ} (hε : 0<ε) :
    ∃ B≥0, ∀ (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) (z : ℂ) (v : ℝ) (hv : 0<v),
      v^2*‖deriv (cubicThetaCuspCutoffSection δ F z) v‖^2≤
        (1+ε)*cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)+
          B*(Icc (1:ℝ) 2).indicator (fun t => ‖cubicThetaSectionFunction F
            (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))‖^2) v := by
  classical
  obtain ⟨B₀,hB₀,hB⟩ := cubicThetaCuspCutoff_deriv_bound
  have he : 0≤1+ε⁻¹ := by positivity
  refine ⟨(1+ε⁻¹)*B₀,mul_nonneg he hB₀,?_⟩
  intro δ F z v hv
  let f : ℝ → ℂ := fun t => cubicThetaSectionFunction F
    (cubicThetaMobius (cubicThetaFullComplex δ) (z,t))
  have hf : DifferentiableAt ℝ f v := cubicThetaCuspRaw_differentiableAt δ F z hv
  have ha := (cubicThetaCuspCutoff_smooth.differentiable (by simp)) v
  have hd : deriv (cubicThetaCuspCutoffSection δ F z) v=
      deriv cubicThetaCuspCutoff v*f v+cubicThetaCuspCutoff v*deriv f v :=
    deriv_mul ha hf
  rw [hd]
  have hy := cubicThetaComplex_norm_add_young
    (deriv cubicThetaCuspCutoff v*f v) (cubicThetaCuspCutoff v*deriv f v) hε
  have hy' := mul_le_mul_of_nonneg_left hy (sq_nonneg v)
  simp only [norm_mul,mul_pow] at hy'
  have hunit : ‖cubicThetaCuspCutoff v‖^2≤1 := by
    nlinarith [cubicThetaCuspCutoff_norm v,_root_.norm_nonneg (cubicThetaCuspCutoff v)]
  have hmain : v^2*(‖cubicThetaCuspCutoff v‖^2*‖deriv f v‖^2)≤
      cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv) := by
    calc
      _ = ‖cubicThetaCuspCutoff v‖^2*(v^2*‖deriv f v‖^2) := by ring
      _ ≤ 1*(v^2*‖deriv f v‖^2) := mul_le_mul_of_nonneg_right hunit
        (mul_nonneg (sq_nonneg v) (sq_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using cubicThetaCuspSection_vertical_energy δ F z hv
  have herr : v^2*(‖deriv cubicThetaCuspCutoff v‖^2*‖f v‖^2)≤
      (Icc (1:ℝ) 2).indicator (fun _ => B₀) v*‖f v‖^2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hB v) (sq_nonneg ‖f v‖)
  calc
    _ ≤ (1+ε)*(v^2*(‖cubicThetaCuspCutoff v‖^2*‖deriv f v‖^2))+
        (1+ε⁻¹)*(v^2*(‖deriv cubicThetaCuspCutoff v‖^2*‖f v‖^2)) := by
      convert hy' using 1
      ring
    _ ≤ (1+ε)*cubicThetaSectionEnergy F (δ • cubicThetaVerticalPoint z v hv)+
        (1+ε⁻¹)*((Icc (1:ℝ) 2).indicator (fun _ => B₀) v*‖f v‖^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
        (mul_le_mul_of_nonneg_left herr he)
    _ = _ := by
      by_cases h : v∈Icc (1:ℝ) 2
      · simp only [indicator_of_mem h]
        dsimp [f]
        ring
      · simp only [indicator_of_notMem h,zero_mul,mul_zero,add_zero]

end CubicFirstMoment

end

end OAI
