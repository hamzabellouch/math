import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarFactorization

namespace OAI

/-! Removing the regular primary common-factor series at the scalar pole. -/
noncomputable section
open scoped Topology
open Filter
namespace CubicFirstMoment

lemma cubicThetaPrimaryMass_continuousOn :
    ContinuousOn cubicThetaPrimaryMass (Set.Ioi 1) := by
  intro t ht
  change 1<t at ht
  let a := (1+t)/2
  have ha : 1<a := by dsimp [a]; linarith
  have hat : a<t := by dsimp [a]; linarith
  have hc : ContinuousOn cubicThetaPrimaryMass (Set.Ici a) := by
    have hf (d : PrimaryArgument) : Continuous (fun u : ℝ => (norm d.val)^(-u)) :=
      (Real.continuous_const_rpow (norm_pos_of_ne_zero
        (primary_ne_zero d.property)).ne').comp continuous_neg
    apply continuousOn_tsum (fun d => (hf d).continuousOn) (cubicThetaPrimaryMass_summable ha)
    intro d u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero d.property))
      (neg_le_neg hu)
  exact (hc.continuousAt (Ici_mem_nhds hat)).continuousWithinAt

lemma cubicThetaPrimaryMass_two :
    (cubicThetaPrimaryMass 2:ℂ)=(8/9:ℂ)*principalIdealZeta 2 := by
  rw [cubicThetaPrimaryMass_euler (by norm_num)]
  congr 1
  norm_num [Complex.cpow_ofNat,Complex.cpow_neg]

lemma cubicThetaScalarEisenstein_ofReal {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    cubicThetaScalarEisenstein p (s:ℂ)=(cubicThetaScalarHeightMass p s:ℂ) := by
  rw [cubicThetaScalarEisenstein,cubicThetaScalarHeightMass,Complex.ofReal_tsum]
  apply tsum_congr
  intro r
  exact (Complex.ofReal_cpow (r.height_pos hp).le s).symm

lemma cubicThetaScalarHeightMass_eq_div {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    cubicThetaScalarHeightMass p s=cubicThetaFullHeightMass p s/cubicThetaPrimaryMass s := by
  rw [cubicThetaFullHeightMass_factorization hp hs]
  field_simp [(cubicThetaPrimaryMass_pos (lt_trans (by norm_num) hs)).ne']

end CubicFirstMoment

end

end OAI
