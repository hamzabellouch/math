import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootResidues

namespace OAI

/-! The normalized average of the actual fractional root operators is a
projection onto the invariant sections. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootAverage {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeRootSections p →ₗ[ℂ] cubicThetaPrimeRootSections p := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  exact (norm p:ℂ)⁻¹ • ∑ r : Residues p,(cubicThetaPrimeRootResidueOperator hp r).toLinearMap

lemma cubicThetaPrimeRootAverage_apply {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootAverage hp F=
      (norm p:ℂ)⁻¹ • ∑ r : Residues p,cubicThetaPrimeRootResidueOperator hp r F := by
  classical
  simp only [cubicThetaPrimeRootAverage,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearEquiv.coe_toLinearMap]
  congr 1
  apply Finset.sum_congr
  · ext r
    simp
  · intro r _
    rfl

theorem cubicThetaPrimeRootAverage_invariant {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootResidueOperator hp r (cubicThetaPrimeRootAverage hp F)=
      cubicThetaPrimeRootAverage hp F := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  simp only [cubicThetaPrimeRootAverage_apply,map_smul,map_sum]
  congr 1
  simp_rw [←cubicThetaPrimeRootResidueOperator_add]
  exact Equiv.sum_comp (Equiv.addLeft r) (fun s => cubicThetaPrimeRootResidueOperator hp s F)

theorem cubicThetaPrimeRootAverage_fixed {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : ∀ r : Residues p,cubicThetaPrimeRootResidueOperator hp r F=F) :
    cubicThetaPrimeRootAverage hp F=F := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  have hcard : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  rw [cubicThetaPrimeRootAverage_apply]
  simp_rw [hF]
  rw [Finset.sum_const,Finset.card_univ,←Nat.cast_smul_eq_nsmul ℂ,smul_smul,hcard,
    inv_mul_cancel₀ hq,one_smul]

theorem cubicThetaPrimeRootAverage_idempotent {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) :
    cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootAverage hp F)=
      cubicThetaPrimeRootAverage hp F :=
  cubicThetaPrimeRootAverage_fixed hp _ (fun r => cubicThetaPrimeRootAverage_invariant hp r F)

end CubicFirstMoment

end

end OAI
