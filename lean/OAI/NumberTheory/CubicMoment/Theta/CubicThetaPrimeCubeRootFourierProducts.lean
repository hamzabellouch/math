import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFourier

namespace OAI

/-! Orthogonal projection algebra for the actual cubic-scale finite action. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootFourierL2_translate {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootResidueL2 hp s F)=
      residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*s) • cubicThetaPrimeCubeRootFourierL2 hp k F := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  let ψ := residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero)
  have hc (r : Residues (p^3)) : star (ψ (k*r))=ψ (k*s)*star (ψ (k*(r+s))) := by
    simp only [ψ,cubicThetaResidueFourier_star]
    rw [←AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [cubicThetaPrimeCubeRootFourierL2_apply]
  simp_rw [←cubicThetaPrimeCubeRootResidueL2_add]
  calc
    _ = (norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),ψ (k*s) •
        (star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [smul_smul,←hc r]
    _ = ψ (k*s) • ((norm (p^3):ℂ)⁻¹ • ∑ r : Residues (p^3),
        star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F) := by
      rw [←Finset.smul_sum,smul_comm]
    _ = _ := by
      have he := Equiv.sum_comp (Equiv.addRight s)
        (fun r => star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r F)
      change (∑ r : Residues (p^3),star (ψ (k*(r+s))) • cubicThetaPrimeCubeRootResidueL2 hp (r+s) F)=
        ∑ r : Residues (p^3),star (ψ (k*r)) • cubicThetaPrimeCubeRootResidueL2 hp r F at he
      rw [he,cubicThetaPrimeCubeRootFourierL2_apply]

lemma cubicThetaPrimeCubeRootFourierL2_commute {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootResidueL2 hp s F) := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hc (r : Residues (p^3)) :
      cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootResidueL2 hp r F)=
        cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootResidueL2 hp s F) := by
    rw [←cubicThetaPrimeCubeRootResidueL2_add,add_comm s r,cubicThetaPrimeCubeRootResidueL2_add]
  simp only [cubicThetaPrimeCubeRootFourierL2_apply,map_smul,map_sum,hc]

lemma cubicThetaPrimeCubeRootFourierL2_eigen {p : Eisenstein} (hp : primaryPrime p)
    (k s : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootResidueL2 hp s (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*s) • cubicThetaPrimeCubeRootFourierL2 hp k F := by
  rw [cubicThetaPrimeCubeRootFourierL2_commute,cubicThetaPrimeCubeRootFourierL2_translate]

theorem cubicThetaPrimeCubeRootFourierL2_product {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp j (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      if j=k then cubicThetaPrimeCubeRootFourierL2 hp k F else 0 := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Fintype (Residues (p^3)) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues (p^3)):ℂ)=(norm (p^3):ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card (pow_ne_zero 3 hp.2.ne_zero)]
    simpa only [Complex.ofReal_natCast] using congrArg Complex.ofReal (normNat_cast (p^3))
  have hsum : (∑ r : Residues (p^3),star (residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (j*r))*
      residueFourierChar (p^3) (pow_ne_zero 3 hp.2.ne_zero) (k*r))=if j=k then (norm (p^3):ℂ) else 0 := by
    simpa only [mul_comm,eq_comm,hcard] using cubicThetaResidueFourier_orthogonal (p^3) (pow_ne_zero 3 hp.2.ne_zero) k j
  rw [cubicThetaPrimeCubeRootFourierL2_apply]
  simp_rw [cubicThetaPrimeCubeRootFourierL2_eigen,smul_smul]
  rw [←Finset.sum_smul,hsum]
  split_ifs
  · rw [smul_smul,inv_mul_cancel₀
      (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero (pow_ne_zero 3 hp.2.ne_zero)).ne'),one_smul]
  · rw [zero_smul,smul_zero]

theorem cubicThetaPrimeCubeRootFourierL2_idempotent {p : Eisenstein} (hp : primaryPrime p)
    (k : Residues (p^3)) (F : cubicThetaPrimeCubeRootAutomorphicL2 hp) :
    cubicThetaPrimeCubeRootFourierL2 hp k (cubicThetaPrimeCubeRootFourierL2 hp k F)=
      cubicThetaPrimeCubeRootFourierL2 hp k F := by
  rw [cubicThetaPrimeCubeRootFourierL2_product,ite_eq_left (Eq.refl k)]


end CubicFirstMoment

end

end OAI
