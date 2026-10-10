import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierL2

namespace OAI

/-! Each completed root Fourier projection is a contraction in the
actual Hilbert norm. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeRootFourierL2_norm_le {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (u : cubicThetaPrimeRootAutomorphicL2 hp) :
    ‖cubicThetaPrimeRootFourierL2 hp k u‖≤‖u‖ := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues p):ℝ)=norm p := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact normNat_cast p
  rw [cubicThetaPrimeRootFourierL2_apply,norm_smul,norm_inv,
    Complex.norm_of_nonneg (norm_nonneg p)]
  calc
    _ ≤ (norm p)⁻¹*∑ r : Residues p,
        ‖star (residueFourierChar p hp.2.ne_zero (k*r)) • cubicThetaPrimeRootResidueL2 hp r u‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (norm_nonneg p))
    _ = ‖u‖ := by
      simp only [norm_smul,norm_star,cubicThetaResidueFourier_norm,
        LinearIsometry.norm_map,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
      rw [inv_mul_cancel_left₀ (norm_pos_of_ne_zero hp.2.ne_zero).ne']

end CubicFirstMoment

end

end OAI
