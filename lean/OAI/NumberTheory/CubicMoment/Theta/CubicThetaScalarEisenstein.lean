import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinConvergence
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBottomRowAction

namespace OAI

/-! The scalar Eisenstein series for the same principal arithmetic group.
It supplies the positive height kernel for the energy unfolding. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaScalarEisenstein (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow,(r.height p:ℂ)^s

lemma cubicThetaScalarEisenstein_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun r : CubicThetaBottomRow => (r.height p:ℂ)^s) := by
  apply Summable.of_norm
  apply (cubicThetaEisenstein_summable hp hs).norm.congr
  intro r
  simp only [cubicThetaEisensteinTerm,norm_mul,norm_star,r.phase_norm,one_mul]

lemma cubicThetaScalarEisenstein_real_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    Summable (fun r : CubicThetaBottomRow => r.height p^s) := by
  have h := (cubicThetaScalarEisenstein_summable hp (s:=(s:ℂ)) (by simpa using hs)).norm
  apply h.congr
  intro r
  exact Complex.norm_cpow_eq_rpow_re_of_pos (r.height_pos hp) _

theorem cubicThetaScalarEisenstein_invariant (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaScalarEisenstein (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaScalarEisenstein p s := by
  unfold cubicThetaScalarEisenstein
  simp_rw [←CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => (r.height p:ℂ)^s)

end CubicFirstMoment

end

end OAI
