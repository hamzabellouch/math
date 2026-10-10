import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRowTransport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspCutoffBounds

namespace OAI

/-! The literal arithmetic difference between Eisenstein and incoming
series, with its absolutely convergent row expansion and all-cusp bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticRemainder (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  cubicThetaEisenstein p s-cubicThetaIncomingEisenstein p s

def cubicThetaRemainderRow (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  (1-cubicThetaCuspCutoff (r.height p))*cubicThetaEisensteinTerm r p s

lemma cubicThetaRemainderRow_eq (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaRemainderRow r p s=cubicThetaEisensteinTerm r p s-cubicThetaIncomingTerm r p s := by
  unfold cubicThetaRemainderRow cubicThetaIncomingTerm
  ring

lemma cubicThetaRemainderRow_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) : Summable (fun r => cubicThetaRemainderRow r p s) := by
  simp_rw [cubicThetaRemainderRow_eq]
  exact (cubicThetaEisenstein_summable hp hs).sub
    (summable_of_hasFiniteSupport (cubicThetaIncomingTerm_finite hp s))

theorem cubicThetaArithmeticRemainder_eq_sum {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    cubicThetaArithmeticRemainder p s=∑' r : CubicThetaBottomRow, cubicThetaRemainderRow r p s := by
  simp_rw [cubicThetaRemainderRow_eq]
  exact ((cubicThetaEisenstein_summable hp hs).tsum_sub
    (summable_of_hasFiniteSupport (cubicThetaIncomingTerm_finite hp s))).symm

lemma cubicThetaArithmeticRemainder_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaArithmeticRemainder p s := by
  unfold cubicThetaArithmeticRemainder
  rw [cubicThetaEisenstein_automorphy g hp,cubicThetaIncomingEisenstein_automorphy g hp]
  ring

lemma cubicThetaRemainderRow_norm (r : CubicThetaBottomRow) {p : ℂ × ℝ}
    (hp : 0<p.2) (s : ℂ) :
    ‖cubicThetaRemainderRow r p s‖≤2*(r.height p)^s.re := by
  have hcut : ‖1-cubicThetaCuspCutoff (r.height p)‖≤2 :=
    (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith [cubicThetaCuspCutoff_norm (r.height p)])
  rw [cubicThetaRemainderRow,norm_mul,cubicThetaEisensteinTerm,norm_mul,norm_star,
    r.phase_norm,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp)]
  exact mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg (r.height_pos hp).le _)

lemma cubicThetaRemainderRow_cusp_zero (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    (r : CubicThetaBottomRow) {p : ℂ × ℝ} (hp : 0<p.2) (hv : 2≤p.2)
    (s : ℂ) (hc : (cubicThetaCuspRow δ r).c=0) :
    cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) p) s=0 := by
  have hh := cubicThetaCuspRow_height δ r hp
  rw [cubicThetaCuspRow_height_zero_c hc] at hh
  unfold cubicThetaRemainderRow
  rw [← hh,cubicThetaCuspCutoff_one hv,sub_self,zero_mul]

lemma cubicThetaRemainderRow_cusp_bound (δ : Matrix.SpecialLinearGroup (Fin 2) Eisenstein)
    (r : CubicThetaBottomRow) (z : ℂ) {v R : ℝ} (hv : 2≤v)
    (hz : Complex.normSq z≤R) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖cubicThetaRemainderRow r (cubicThetaMobius (cubicThetaFullComplex δ) (z,v)) s‖≤
      (2*(3+2*R)^2*v^(4-s.re))*
        (norm (cubicThetaCuspRow δ r).c)^(-(s.re-2))*
          (1+norm (cubicThetaCuspRow δ r).d)^(-2:ℝ) := by
  have hv0 : 0<v := by linarith
  have hnc := norm_nonneg (cubicThetaCuspRow δ r).c
  have hnd := norm_nonneg (cubicThetaCuspRow δ r).d
  by_cases hc : (cubicThetaCuspRow δ r).c=0
  · rw [cubicThetaRemainderRow_cusp_zero δ r (p:=(z,v)) hv0 hv s hc,norm_zero]
    positivity
  · have hb := cubicThetaRemainderRow_norm r
      (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (p:=(z,v)) hv0) s
    rw [← cubicThetaCuspRow_height δ r (p:=(z,v)) hv0] at hb
    have h := cubicThetaCuspRowHeight_power hc (cubicThetaCuspRow δ r).d z
      (by linarith : 1≤v) hz hs
    exact hb.trans ((mul_le_mul_of_nonneg_left h (by norm_num)).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
