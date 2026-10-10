import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveAction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarRankinKernel

namespace OAI

/-! A positive full-group kernel majorizing the principal scalar kernel.
Its right action allows the estimate to be proved in one Siegel set. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaPrimitiveRow.norm_le_denominator (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    1+norm r.c+norm r.d ≤ cubicThetaHeightConstant p*r.denominator p := by
  have hnorm : 1 ≤ norm r.c+norm r.d := by
    rcases r.coprime.ne_zero_or_ne_zero with hc | hd
    · linarith [one_le_norm hc,norm_nonneg r.d]
    · linarith [one_le_norm hd,norm_nonneg r.c]
  have h := r.norm_sum_bound hp
  unfold cubicThetaHeightConstant
  nlinarith

lemma CubicThetaPrimitiveRow.height_le (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    r.height p ≤ (p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d) := by
  apply (div_le_div_iff₀ (r.denominator_pos hp) (by linarith [norm_nonneg r.c,norm_nonneg r.d])).mpr
  have h := mul_le_mul_of_nonneg_left (r.norm_le_denominator hp) hp.le
  convert h using 1
  ring

lemma cubicThetaPrimitiveHeight_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) : Summable (fun r : CubicThetaPrimitiveRow => r.height p^s) := by
  have hC := cubicThetaHeightConstant_pos hp
  have hsum := summable_eisenstein_one_add_norm (show 1<s/2 by linarith)
  have hprod : Summable (fun cd : Eisenstein × Eisenstein =>
      (1+norm cd.1)^(-(s/2))*(1+norm cd.2)^(-(s/2))) :=
    summable_mul_of_summable_norm hsum.norm hsum.norm
  have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
    intro r t h
    exact CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  apply ((hprod.mul_left ((p.2*cubicThetaHeightConstant p)^s)).comp_injective hi).of_nonneg_of_le
  · intro r
    exact Real.rpow_nonneg (r.height_pos hp).le _
  · intro r
    dsimp only [Function.comp_apply]
    have hN : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
    calc
      _  ≤  ((p.2*cubicThetaHeightConstant p)/(1+norm r.c+norm r.d))^s :=
        Real.rpow_le_rpow (r.height_pos hp).le (r.height_le hp) (by linarith)
      _ = (p.2*cubicThetaHeightConstant p)^s*(1+norm r.c+norm r.d)^(-s) := by
        rw [Real.div_rpow (mul_pos hp hC).le hN.le,Real.rpow_neg hN.le]
        rfl
      _  ≤  _ := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_left
          (cubicTheta_two_norm_decay (norm_nonneg r.c) (norm_nonneg r.d) (by linarith : 0 ≤ s))
          (Real.rpow_nonneg (mul_pos hp hC).le _)

def cubicThetaPrimitiveKernel (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaPrimitiveRow,if r.height p ≤ 1 then r.height p^s else 0

lemma cubicThetaPrimitiveKernel_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    Summable (fun r : CubicThetaPrimitiveRow => if r.height p ≤ 1 then r.height p^s else 0) := by
  apply (cubicThetaPrimitiveHeight_summable hp hs).of_nonneg_of_le
  · intro r
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl
  · intro r
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (r.height_pos hp).le _

lemma cubicThetaPrimitiveKernel_invariant (g : SL(2,Eisenstein))
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    cubicThetaPrimitiveKernel (cubicThetaMobius (cubicThetaFullComplex g) p) s=
      cubicThetaPrimitiveKernel p s := by
  unfold cubicThetaPrimitiveKernel
  simp_rw [←CubicThetaPrimitiveRow.height_rightMul _ g hp]
  exact (CubicThetaPrimitiveRow.rightMulEquiv g).tsum_eq
    (fun r => if r.height p ≤ 1 then r.height p^s else (0:ℝ))

lemma cubicThetaScalarHeightCutoff_le_primitive {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) : cubicThetaScalarHeightCutoff p s ≤ cubicThetaPrimitiveKernel p s := by
  let f : CubicThetaBottomRow → CubicThetaPrimitiveRow := fun r => ⟨r.c,r.d,r.coprime⟩
  have hi : Function.Injective f := by
    intro r t h
    exact CubicThetaBottomRow.ext (congrArg CubicThetaPrimitiveRow.c h)
      (congrArg CubicThetaPrimitiveRow.d h)
  have hsum := cubicThetaPrimitiveKernel_summable hp hs
  have hpull := hsum.comp_injective hi
  have h := hpull.tsum_le_tsum_of_inj f hi (fun r _ => by
    split_ifs
    · exact Real.rpow_nonneg (r.height_pos hp).le _
    · exact le_rfl) (fun r => le_rfl) hsum
  exact h

end CubicFirstMoment

end

end OAI
