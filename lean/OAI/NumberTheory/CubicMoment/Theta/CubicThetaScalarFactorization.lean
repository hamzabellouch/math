import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveRowFactorization

namespace OAI

/-! Exact removal of common primary factors from the scalar height series. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaScalarHeightMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaBottomRow,r.height p^s

def cubicThetaFullHeightMass (p : ℂ × ℝ) (s : ℝ) : ℝ :=
  ∑' r : CubicThetaFullRow,r.height p^s

lemma cubicThetaFullRowMultiply_rpow (g : PrimaryArgument) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℝ) :
    (cubicThetaFullRowMultiply g r).height p^s=(norm g.val)^(-s)*r.height p^s := by
  rw [cubicThetaFullRowMultiply_height,
    Real.mul_rpow (inv_nonneg.mpr (norm_nonneg _)) (r.height_pos hp).le,
    Real.inv_rpow (norm_nonneg _),←Real.rpow_neg (norm_nonneg _)]

lemma cubicThetaFullHeightMass_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) : Summable (fun r : CubicThetaFullRow => r.height p^s) := by
  have hg := cubicThetaPrimaryMass_summable (lt_trans (by norm_num) hs)
  have hr := cubicThetaScalarEisenstein_real_summable hp hs
  have hprod : Summable (fun z : PrimaryArgument × CubicThetaBottomRow =>
      (norm z.1.val)^(-s)*z.2.height p^s) :=
    summable_mul_of_summable_norm hg.norm hr.norm
  have ht : Summable (fun z : PrimaryArgument × CubicThetaBottomRow =>
      (cubicThetaPrimitiveRowEquiv z).height p^s) := hprod.congr
        (fun z => (cubicThetaFullRowMultiply_rpow z.1 z.2 hp s).symm)
  have hc := ht.comp_injective cubicThetaPrimitiveRowEquiv.symm.injective
  apply hc.congr
  intro r
  change (cubicThetaPrimitiveRowEquiv (cubicThetaPrimitiveRowEquiv.symm r)).height p^s=_
  rw [Equiv.apply_symm_apply]

theorem cubicThetaFullHeightMass_factorization {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    cubicThetaFullHeightMass p s=cubicThetaPrimaryMass s*cubicThetaScalarHeightMass p s := by
  have hg := cubicThetaPrimaryMass_summable (lt_trans (by norm_num) hs)
  have hr := cubicThetaScalarEisenstein_real_summable hp hs
  unfold cubicThetaFullHeightMass
  rw [←cubicThetaPrimitiveRowEquiv.tsum_eq (fun r => r.height p^s)]
  simp_rw [show ∀ z : PrimaryArgument × CubicThetaBottomRow,
      (cubicThetaPrimitiveRowEquiv z).height p^s=(norm z.1.val)^(-s)*z.2.height p^s from
    fun z => cubicThetaFullRowMultiply_rpow z.1 z.2 hp s]
  exact (summable_mul_of_summable_norm hg.norm hr.norm).tsum_prod.trans
    (by
      dsimp only
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
      rfl)

end CubicFirstMoment

end

end OAI
