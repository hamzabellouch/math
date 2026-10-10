import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierProducts

namespace OAI

/-! The actual finite Fourier projections resolve every root-cover section. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaPrimeRootFourierProjection_sum {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p) :
    (∑ k : Residues p,cubicThetaPrimeRootFourierProjection hp k F)=F := by
  classical
  have hcard : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  have hs (r : Residues p) :
      (∑ k : Residues p,star (residueFourierChar p hp.2.ne_zero (k*r)))=
        if r=0 then (norm p:ℂ) else 0 := by
    simpa only [mul_zero,AddChar.map_zero_eq_one,one_mul,eq_comm,hcard] using
      cubicThetaResidueFourier_orthogonal p hp.2.ne_zero 0 r
  simp only [cubicThetaPrimeRootFourierProjection_apply]
  rw [←Finset.smul_sum,Finset.sum_comm]
  simp_rw [←Finset.sum_smul,hs]
  simp only [ite_smul,zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true,cubicThetaPrimeRootResidueOperator_zero,
    smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'),one_smul]

end CubicFirstMoment

end

end OAI
