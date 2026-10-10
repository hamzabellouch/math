import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCount

namespace OAI

/-! The six units and the exact index of primary invertible residues. -/
noncomputable section
namespace CubicFirstMoment

lemma eisenstein_unit_pow_six (u : Eisensteinˣ) : u^6=1 := by
  apply Units.ext
  change (u:Eisenstein)^6=1
  have hp (j : ℕ) : (omegaE^j)^6=1 := by
    have hc : (omegaE^j)^3=1 := by
      rw [←pow_mul,Nat.mul_comm j 3,pow_mul,omegaE_cube,one_pow]
    calc
      _ = ((omegaE^j)^3)^2 := by ring
      _ = 1 := by rw [hc]; norm_num
  obtain ⟨j,hj | hj⟩ := eisenstein_unit_eq_signed_omega u.isUnit
  · rw [hj]; exact hp j
  · rw [hj,neg_pow,show (-1:Eisenstein)^6=1 by norm_num,one_mul]
    exact hp j

lemma eisenstein_neg_omega_primitive : IsPrimitiveRoot (-omegaE) 6 := by
  have hm := IsPrimitiveRoot.neg_one (R:=Eisenstein) 0 (by norm_num : (0:ℕ) ≠ 2)
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hcop : (orderOf (-1:Eisenstein)).Coprime (orderOf omegaE) := by
    rw [←hm.eq_orderOf,←omegaE_primitive.eq_orderOf]
    decide
  rw [show -omegaE=(-1:Eisenstein)*omegaE by ring,
    (Commute.all (-1:Eisenstein) omegaE).orderOf_mul_eq_mul_orderOf_of_coprime hcop,
    ←hm.eq_orderOf,←omegaE_primitive.eq_orderOf]

def eisensteinUnitsEquivSixthRoots : Eisensteinˣ ≃ rootsOfUnity 6 Eisenstein where
  toFun u := ⟨u,by exact eisenstein_unit_pow_six u⟩
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

lemma eisenstein_units_card : Nat.card Eisensteinˣ=6 := by
  rw [Nat.card_congr eisensteinUnitsEquivSixthRoots]
  exact eisenstein_neg_omega_primitive.card_rootsOfUnity

def eisensteinUnitReductionThree : Eisensteinˣ →* (Residues (3:Eisenstein))ˣ :=
  Units.map (Ideal.Quotient.mk (modulus 3)).toMonoidHom

lemma eisensteinUnitReductionThree_bijective : Function.Bijective eisensteinUnitReductionThree := by
  constructor
  · intro u v huv
    have hq : Ideal.Quotient.mk (modulus 3) ((u:Eisenstein)*(↑v⁻¹:Eisenstein))=1 := by
      have he : Ideal.Quotient.mk (modulus 3) (u:Eisenstein)=
          Ideal.Quotient.mk (modulus 3) (v:Eisenstein) :=
        congrArg (fun x : (Residues (3:Eisenstein))ˣ => (x:Residues 3)) huv
      rw [map_mul,he,←map_mul]
      simp
    have hp := primary_unit_eq_one (u*v⁻¹).isUnit ((primary_iff_residue_one _).mpr hq)
    have he : u*v⁻¹=1 := Units.ext hp
    exact mul_inv_eq_one.mp he
  · intro x
    obtain ⟨u,hu,hp⟩ := unit_lift_mod_three
      (show IsUnit (Ideal.Quotient.mk (modulus 3) (residueRepresentative 3 (x:Residues 3))) by
        rw [residueRepresentative_spec]; exact x.isUnit)
    refine ⟨hu.unit⁻¹,?_⟩
    apply Units.ext
    have he := (primary_iff_residue_one _).mp hp
    rw [map_mul,residueRepresentative_spec] at he
    have hq : Ideal.Quotient.mk (modulus 3) u =
        (eisensteinUnitReductionThree hu.unit : Residues 3) := by
      change _ = Ideal.Quotient.mk (modulus 3) (hu.unit:Eisenstein)
      rw [hu.unit_spec]
    rw [hq] at he
    have he' : x*eisensteinUnitReductionThree hu.unit=1 := Units.ext he
    have hx := eq_inv_of_mul_eq_one_left he'
    simpa only [map_inv] using congrArg (fun v : (Residues (3:Eisenstein))ˣ => (v:Residues 3)) hx.symm

lemma cubicTheta_residue_three_units_card : Nat.card (Residues (3:Eisenstein))ˣ=6 := by
  rw [←Nat.card_congr (Equiv.ofBijective _ eisensteinUnitReductionThree_bijective)]
  exact eisenstein_units_card

theorem cubicTheta_primaryResidue_six {c : Eisenstein} (hc : c≠0) :
    Nat.card (Residues (3*c))ˣ=6*Nat.card (CubicThetaPrimaryResidue c) := by
  rw [cubicThetaPrimaryResidue_card hc,cubicTheta_residue_three_units_card]

theorem cubicThetaEisenstein_constant_units {c : Eisenstein} (hc : c≠0)
    (hcb : ∃ j : Eisenstein, j^3=c) :
    cubicThetaEisensteinGaussCoefficient c 0=(Nat.card (Residues (3*c))ˣ:ℂ)/6 := by
  rw [cubicThetaEisenstein_constant_card hc hcb,cubicTheta_primaryResidue_six hc]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
