import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantSupport
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueConductorKernel

namespace OAI

/-! The constant coefficient on cubes as the kernel size of the actual
reduction of residue units to modulus three. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaReductionThree (c : Eisenstein) : Residues (3*c) →+* Residues 3 :=
  residueReduction (show (3:Eisenstein) ∣ 3*c from ⟨c,rfl⟩)

def cubicThetaUnitReductionThree (c : Eisenstein) : (Residues (3*c))ˣ →* (Residues 3)ˣ :=
  Units.map (cubicThetaReductionThree c).toMonoidHom

abbrev CubicThetaPrimaryResidue (c : Eisenstein) :=
  {x : Residues (3*c) // IsUnit x ∧ cubicThetaReductionThree c x = 1}

lemma cubicTheta_primaryResidue_iff (c : Eisenstein) (x : Residues (3*c)) :
    (primary (residueRepresentative (3*c) x) ∧
      IsCoprime c (residueRepresentative (3*c) x)) ↔
      (IsUnit x ∧ cubicThetaReductionThree c x = 1) := by
  have hred : Ideal.Quotient.mk (modulus 3) (residueRepresentative (3*c) x) =
      cubicThetaReductionThree c x := by
    change residueReduction (show (3:Eisenstein) ∣ 3*c from ⟨c,rfl⟩)
      (Ideal.Quotient.mk (modulus (3*c)) (residueRepresentative (3*c) x)) = _
    rw [residueRepresentative_spec]
    rfl
  constructor
  · rintro ⟨hp,hc⟩
    refine ⟨?_,?_⟩
    · have hu := residue_isUnit_of_isCoprime ((primary_coprime_three hp).symm.mul_left hc)
      rwa [residueRepresentative_spec] at hu
    · rw [←hred]
      exact (primary_iff_residue_one _).mp hp
  · rintro ⟨hu,hr⟩
    refine ⟨(primary_iff_residue_one _).mpr (hred.trans hr),?_⟩
    have hcop : IsCoprime (3*c) (residueRepresentative (3*c) x) :=
      isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
    exact hcop.of_mul_left_right

def cubicThetaPrimaryResidueEquivKernel (c : Eisenstein) :
    CubicThetaPrimaryResidue c ≃ (cubicThetaUnitReductionThree c).ker where
  toFun x := ⟨x.property.1.unit, by
    apply Units.ext
    change cubicThetaReductionThree c (x.property.1.unit : Residues (3*c)) = 1
    rw [x.property.1.unit_spec]
    exact x.property.2⟩
  invFun u := ⟨(u.val : Residues (3*c)),u.val.isUnit,by
    have he := congrArg (fun v : (Residues 3)ˣ => (v : Residues 3))
      ((MonoidHom.mem_ker).mp u.property)
    exact he⟩
  left_inv x := by
    apply Subtype.ext
    exact x.property.1.unit_spec
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact IsUnit.unit_spec _

theorem cubicThetaPrimaryResidue_card {c : Eisenstein} (hc : c ≠ 0) :
    Nat.card (Residues (3*c))ˣ =
      Nat.card (Residues (3:Eisenstein))ˣ*Nat.card (CubicThetaPrimaryResidue c) := by
  let f := cubicThetaUnitReductionThree c
  have hf : Function.Surjective f := residueReduction_units_surjective
    (mul_ne_zero (by norm_num) hc) ⟨c,rfl⟩
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at he
  rw [Nat.card_congr (cubicThetaPrimaryResidueEquivKernel c)]
  exact he

theorem cubicThetaEisenstein_constant_card {c : Eisenstein} (hc : c ≠ 0)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0 = (Nat.card (CubicThetaPrimaryResidue c):ℂ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  rw [cubicThetaEisenstein_constant_cube hcb]
  simp_rw [cubicTheta_primaryResidue_iff]
  rw [tsum_fintype, Nat.card_eq_fintype_card]
  change (∑ x : Residues (3*c), if IsUnit x ∧ cubicThetaReductionThree c x = 1 then (1:ℂ) else 0) =
    (Fintype.card {x : Residues (3*c) // IsUnit x ∧ cubicThetaReductionThree c x = 1}:ℂ)
  rw [Fintype.card_subtype]
  simp

end CubicFirstMoment

end

end OAI
