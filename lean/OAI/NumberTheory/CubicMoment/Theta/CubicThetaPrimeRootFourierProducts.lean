import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierOperators

namespace OAI

/-! The finite Fourier operators are genuine mutually annihilating
projections on the actual root-section space. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFourierProjection_commute {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootResidueOperator hp s (cubicThetaPrimeRootFourierProjection hp k F)=
      cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootResidueOperator hp s F) := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  have hc (r : Residues p) :
      cubicThetaPrimeRootResidueOperator hp s (cubicThetaPrimeRootResidueOperator hp r F)=
        cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootResidueOperator hp s F) := by
    rw [←cubicThetaPrimeRootResidueOperator_add,add_comm s r,cubicThetaPrimeRootResidueOperator_add]
  simp only [cubicThetaPrimeRootFourierProjection_apply,map_smul,map_sum,hc]

lemma cubicThetaPrimeRootFourierProjection_eigen {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootResidueOperator hp s (cubicThetaPrimeRootFourierProjection hp k F)=
      residueFourierChar p hp.2.ne_zero (k*s) • cubicThetaPrimeRootFourierProjection hp k F := by
  rw [cubicThetaPrimeRootFourierProjection_commute,cubicThetaPrimeRootFourierProjection_translate]

theorem cubicThetaPrimeRootFourierProjection_product {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootFourierProjection hp j (cubicThetaPrimeRootFourierProjection hp k F)=
      if j=k then cubicThetaPrimeRootFourierProjection hp k F else 0 := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  have hsum : (∑ r : Residues p,star (residueFourierChar p hp.2.ne_zero (j*r))*
      residueFourierChar p hp.2.ne_zero (k*r))=if j=k then (norm p:ℂ) else 0 := by
    simpa only [mul_comm,eq_comm,hcard] using cubicThetaResidueFourier_orthogonal p hp.2.ne_zero k j
  rw [cubicThetaPrimeRootFourierProjection_apply]
  simp_rw [cubicThetaPrimeRootFourierProjection_eigen,smul_smul]
  rw [←Finset.sum_smul,hsum]
  split_ifs <;> simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero))]

theorem cubicThetaPrimeRootFourierProjection_idempotent {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootFourierProjection hp k (cubicThetaPrimeRootFourierProjection hp k F)=
      cubicThetaPrimeRootFourierProjection hp k F := by
  rw [cubicThetaPrimeRootFourierProjection_product,ite_eq_left (Eq.refl k)]

end CubicFirstMoment

end

end OAI
