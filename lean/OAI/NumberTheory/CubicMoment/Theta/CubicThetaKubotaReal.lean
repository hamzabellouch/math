import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaCharacter

namespace OAI

/-! The multiplier is trivial on the real part of the principal group,
as required for its eventual extension across SL(2,Z). -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaKubotaValue_conjugate_fixed (g : cubicThetaPrincipalGroup)
    (ha : conjugate (g.val 0 0) = g.val 0 0)
    (hc : conjugate (g.val 1 0) = g.val 1 0) :
    star (cubicThetaKubotaValue g) = cubicThetaKubotaValue g := by
  rw [cubicThetaKubotaValue_eq_symbol]
  have he := cubicSymbol_conjugate (cubicThetaPrincipalGroup_diagonal_primary g).1 (g.val 1 0)
  rw [ha,hc] at he
  exact he.symm

theorem cubicThetaKubotaValue_real (g : cubicThetaPrincipalGroup)
    (ha : conjugate (g.val 0 0) = g.val 0 0)
    (hc : conjugate (g.val 1 0) = g.val 1 0) : cubicThetaKubotaValue g = 1 := by
  have hstar := cubicThetaKubotaValue_conjugate_fixed g ha hc
  have hnorm := cubicThetaKubotaValue_norm g
  have hsq : cubicThetaKubotaValue g^2 = 1 := by
    calc
      _ = cubicThetaKubotaValue g*star (cubicThetaKubotaValue g) := by rw [hstar,pow_two]
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [hnorm]; norm_num
  have hcube := cubicThetaKubotaCharacter_cube g
  change cubicThetaKubotaValue g^3 = 1 at hcube
  calc
    _ = cubicThetaKubotaValue g^3 := by rw [pow_succ,hsq,one_mul]
    _ = 1 := hcube

end CubicFirstMoment

end

end OAI
