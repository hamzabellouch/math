import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspHeatBound

namespace OAI

/-! The literal two-coordinate Gaussian behind the nonzero-first-row bound. -/
noncomputable section
namespace CubicFirstMoment

abbrev CubicThetaNonzeroRow := {c : Eisenstein // c≠0} × Eisenstein

def cubicThetaNonzeroRowQuadratic (p : ℂ × ℝ) (r : CubicThetaNonzeroRow) : ℝ :=
  Complex.normSq ((r.1.val:ℂ)*p.1+r.2)/p.2+norm r.1.val*p.2

def cubicThetaNonzeroRowHeatTerm (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaNonzeroRow) : ℝ :=
  Real.exp (-t*cubicThetaNonzeroRowQuadratic p r)

lemma cubicThetaNonzeroRowHeatTerm_factor {p : ℂ × ℝ} (hp : 0<p.2)
    (t : ℝ) (c : {c : Eisenstein // c≠0}) (d : Eisenstein) :
    cubicThetaNonzeroRowHeatTerm p t (c,d)=Real.exp (-(t*p.2)*norm c.val)*
      Real.exp (-(t/(9*p.2))*Complex.normSq (3*(c.val:ℂ)*p.1+3*(d:ℂ))) := by
  have he : 3*(c.val:ℂ)*p.1+3*(d:ℂ)=3*((c.val:ℂ)*p.1+d) := by ring
  rw [he,Complex.normSq_mul,show Complex.normSq (3:ℂ)=9 by norm_num]
  rw [←Real.exp_add]
  unfold cubicThetaNonzeroRowHeatTerm cubicThetaNonzeroRowQuadratic
  congr 1
  field_simp
  ring

lemma cubicThetaNonzeroRowHeatTerm_row_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) (c : {c : Eisenstein // c≠0}) :
    Summable (fun d : Eisenstein => cubicThetaNonzeroRowHeatTerm p t (c,d)) := by
  simp_rw [cubicThetaNonzeroRowHeatTerm_factor hp]
  exact (cubicThetaScalarGaussianReal_summable (3*(c.val:ℂ)*p.1) (by positivity)).mul_left _

lemma cubicThetaNonzeroRowHeatTerm_row (p : ℂ × ℝ) (hp : 0<p.2)
    (t : ℝ) (c : {c : Eisenstein // c≠0}) :
    (∑' d : Eisenstein,cubicThetaNonzeroRowHeatTerm p t (c,d))=
      Real.exp (-(t*p.2)*norm c.val)*cubicThetaScalarGaussianReal (3*(c.val:ℂ)*p.1) (t/(9*p.2)) := by
  simp_rw [cubicThetaNonzeroRowHeatTerm_factor hp]
  rw [tsum_mul_left]
  rfl

lemma cubicThetaNonzeroRowHeatTerm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) : Summable (cubicThetaNonzeroRowHeatTerm p t) := by
  apply (summable_prod_of_nonneg (f:=cubicThetaNonzeroRowHeatTerm p t)
    (fun r => (Real.exp_pos _).le)).mpr
  constructor
  · exact cubicThetaNonzeroRowHeatTerm_row_summable hp ht
  · simp_rw [cubicThetaNonzeroRowHeatTerm_row p hp]
    exact cubicThetaNonzeroFirstHeat_summable hp ht

theorem cubicThetaNonzeroRowHeatTerm_tsum {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    (∑' r : CubicThetaNonzeroRow,cubicThetaNonzeroRowHeatTerm p t r)=
      cubicThetaNonzeroFirstHeat p t := by
  rw [(cubicThetaNonzeroRowHeatTerm_summable hp ht).tsum_prod]
  simp_rw [cubicThetaNonzeroRowHeatTerm_row p hp]
  rfl

end CubicFirstMoment

end

end OAI
