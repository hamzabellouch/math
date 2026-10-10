import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitivePower
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticRemainder

namespace OAI

/-! In a high cusp, the incoming term cancels precisely the constant
rows. The remaining literal terms are smooth primitive height powers. -/
noncomputable section
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

def cubicThetaHighCuspRow (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  if (cubicThetaCuspRow δ r).c=0 then 0
  else star r.phase*cubicThetaPrimitivePower (cubicThetaCuspRow δ r) p s

lemma cubicThetaHighCuspRow_eq (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 2≤p.2) (s : ℂ) :
    cubicThetaHighCuspRow δ r p s=
      cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s := by
  have hp0 : 0<p.2 := by linarith
  classical
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · rw [cubicThetaHighCuspRow,ite_eq_left hc,cubicThetaRemainderRow_cusp_zero δ r hp0 hp s hc]
  · have hh : (cubicThetaCuspRow δ r).height p≤1 := by
      apply le_of_not_gt
      intro h
      apply hc
      exact cubicThetaMobius_high_overlap (r.completion.val*δ) (by linarith)
        (by rwa [← cubicThetaPrimitiveRow_height])
    rw [cubicThetaHighCuspRow,ite_eq_right hc,cubicThetaRemainderRow,
      ← cubicThetaCuspRow_height δ r hp0,cubicThetaCuspCutoff_zero hh,sub_zero,one_mul]
    change star r.phase*((cubicThetaCuspRow δ r).height p:ℂ)^s=
      star r.phase*(r.height (cubicThetaMobius (cubicThetaFullComplex δ) p):ℂ)^s
    rw [cubicThetaCuspRow_height δ r hp0]

lemma cubicThetaHighCuspRow_contDiffAt (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaHighCuspRow δ r q s) p := by
  classical
  unfold cubicThetaHighCuspRow
  split_ifs
  · exact contDiffAt_const
  · exact contDiffAt_const.mul (cubicThetaPrimitivePower_contDiffAt _ s hp)

lemma cubicThetaHighCuspRow_fderiv_bound (δ : SL(2,Eisenstein)) (r : CubicThetaBottomRow)
    (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖≤
      3*(‖cubicThetaHighCuspRow δ r p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  classical
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · simp only [cubicThetaHighCuspRow,ite_eq_left hc,fderiv_const_apply,norm_zero,zero_mul,mul_zero,le_refl]
  · have hdP := (cubicThetaPrimitivePower_contDiffAt (cubicThetaCuspRow δ r) s hp).differentiableAt (by simp)
    have hd := hdP.hasFDerivAt.const_mul (star r.phase)
    simp only [cubicThetaHighCuspRow,ite_eq_right hc]
    rw [hd.fderiv,norm_smul,norm_star,r.phase_norm,one_mul,norm_mul,norm_star,r.phase_norm,one_mul]
    exact cubicThetaPrimitivePower_fderiv_bound _ s hp

end CubicFirstMoment

end

end OAI
