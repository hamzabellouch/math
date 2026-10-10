import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridJets

namespace OAI

/-! A joint Frechet derivative bound for the actual Eisenstein summands.
The three proved coordinate bounds control the product-space operator norm. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaComplexProduct_opNorm_le (L : (ℂ × ℝ) →L[ℝ] ℂ) {B : ℝ}
    (hB : 0≤B) (hx : ‖L (1,0)‖≤B) (hy : ‖L (Complex.I,0)‖≤B)
    (hv : ‖L (0,1)‖≤B) : ‖L‖≤3*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hu : u=u.1.re • ((1:ℂ),(0:ℝ))+u.1.im • ((Complex.I:ℂ),(0:ℝ))+u.2 • ((0:ℂ),(1:ℝ)) := by
    apply Prod.ext
    · change u.1=(u.1.re:ℂ)*1+(u.1.im:ℂ)*Complex.I+(u.2:ℂ)*0
      simpa only [mul_one,mul_zero,add_zero] using (Complex.re_add_im u.1).symm
    · simp
  have hr : ‖u.1.re‖≤‖u‖ := (Complex.abs_re_le_norm u.1).trans (norm_fst_le u)
  have hi : ‖u.1.im‖≤‖u‖ := (Complex.abs_im_le_norm u.1).trans (norm_fst_le u)
  have ht : ‖u.2‖≤‖u‖ := norm_snd_le u
  calc
    ‖L u‖=‖u.1.re • L (1,0)+u.1.im • L (Complex.I,0)+u.2 • L (0,1)‖ := by
      conv_lhs => rw [hu,map_add,map_add,map_smul,map_smul,map_smul]
    _ ≤ ‖u.1.re • L (1,0)‖+‖u.1.im • L (Complex.I,0)‖+‖u.2 • L (0,1)‖ := norm_add₃_le
    _ ≤ ‖u‖*B+‖u‖*B+‖u‖*B := by
      simp only [norm_smul]
      exact add_le_add (add_le_add (mul_le_mul hr hx (_root_.norm_nonneg _) (_root_.norm_nonneg _))
        (mul_le_mul hi hy (_root_.norm_nonneg _) (_root_.norm_nonneg _)))
        (mul_le_mul ht hv (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    _ = (3*B)*‖u‖ := by ring

lemma cubicThetaFDeriv_coordinates {F : ℂ × ℝ → ℂ} (x y v : ℝ)
    (hF : DifferentiableAt ℝ F (cubicThetaCartesianPoint x y v)) :
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (1,0)=
      deriv (fun t => F (cubicThetaCartesianPoint t y v)) x ∧
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (Complex.I,0)=
      deriv (fun t => F (cubicThetaCartesianPoint x t v)) y ∧
    (fderiv ℝ F (cubicThetaCartesianPoint x y v)) (0,1)=
      deriv (fun t => F (cubicThetaCartesianPoint x y t)) v := by
  have hx : HasDerivAt (fun t => cubicThetaCartesianPoint t y v) ((1:ℂ),(0:ℝ)) x := by
    simpa only [cubicThetaCartesianPoint,Complex.ofRealCLM_apply,Complex.ofReal_one] using
      ((Complex.ofRealCLM.hasDerivAt (x:=x)).add_const ((y:ℂ)*Complex.I)).prodMk (hasDerivAt_const x v)
  have hy : HasDerivAt (fun t => cubicThetaCartesianPoint x t v) (Complex.I,(0:ℝ)) y := by
    simpa only [cubicThetaCartesianPoint,Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using
      (((Complex.ofRealCLM.hasDerivAt (x:=y)).mul_const Complex.I).const_add (x:ℂ)).prodMk
        (hasDerivAt_const y v)
  have hv : HasDerivAt (fun t => cubicThetaCartesianPoint x y t) ((0:ℂ),(1:ℝ)) v := by
    exact (hasDerivAt_const v ((x:ℂ)+(y:ℂ)*Complex.I)).prodMk (hasDerivAt_id v)
  exact ⟨(hF.hasFDerivAt.comp_hasDerivAt x hx).deriv.symm,
    (hF.hasFDerivAt.comp_hasDerivAt y hy).deriv.symm,
    (hF.hasFDerivAt.comp_hasDerivAt v hv).deriv.symm⟩

lemma cubicThetaEisensteinTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaEisensteinTerm r q s) p := by
  exact contDiffAt_const.mul ((cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p
    (r.height_contDiffAt hp))

lemma cubicThetaEisensteinGridTerm_contDiffAt (cd : Eisenstein × Eisenstein) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaEisensteinGridTerm cd q s) p := by
  classical
  by_cases hc : cubicThetaAdmissiblePair cd
  · have he : (fun q => cubicThetaEisensteinGridTerm cd q s)=
        (fun q => cubicThetaEisensteinTerm (cubicThetaBottomRowEquiv.symm ⟨cd,hc⟩) q s) :=
      funext (fun q => cubicThetaEisensteinGridTerm_admissible ⟨cd,hc⟩ q s)
    rw [he]
    exact cubicThetaEisensteinTerm_contDiffAt _ s hp
  · simp only [cubicThetaEisensteinGridTerm,hc,ite_false]
    exact contDiffAt_const

theorem cubicThetaEisensteinGridTerm_fderiv_bound
    (cd : Eisenstein × Eisenstein) (s : ℂ) {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaEisensteinGridTerm cd q s) p‖≤
      3*(‖cubicThetaEisensteinGridTerm cd p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  have he : cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
    apply Prod.ext
    · exact Complex.re_add_im p.1
    · rfl
  have hd := (cubicThetaEisensteinGridTerm_contDiffAt cd s hp).differentiableAt (by simp)
  have hc := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 (he ▸ hd)
  rw [he] at hc
  have hj := cubicThetaEisensteinGrid_jetBound cd.1 cd.2 s p.1.re p.1.im hp
  apply cubicThetaComplexProduct_opNorm_le _
    (mul_nonneg (_root_.norm_nonneg _) (div_nonneg (cubicThetaJetConstants_nonneg s).1 hp.le))
  · rw [hc.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .x).1
  · rw [hc.2.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .y).1
  · rw [hc.2.2]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .height).1

end CubicFirstMoment

end

end OAI
