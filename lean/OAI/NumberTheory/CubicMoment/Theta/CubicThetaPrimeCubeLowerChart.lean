import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeCosets

namespace OAI

/-! The lower-unipotent chart covers precisely the cosets whose bottom
right entry is a unit at the chosen prime. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeLowerChart_covers {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrincipalGroup) (hd : ¬p ∣ g.val 1 1) :
    ∃ r : Residues (p^3), cubicThetaPrimeCubeLowerChart p r=cubicThetaPrimeCubeCoset p g := by
  let q := Ideal.Quotient.mk (modulus (p^3))
  have hpd : IsCoprime (p^3) (g.val 1 1) :=
    (hp.2.coprime_iff_not_dvd.mpr hd).pow_left
  let d : (Residues (p^3))ˣ := (residue_isUnit_of_isCoprime hpd).unit
  let t : (Residues (p^3))ˣ :=
    (residue_isUnit_of_isCoprime (primary_coprime_three (cubicThetaPrimeCube_primary hp))).unit
  let r : Residues (p^3) := ((d*t)⁻¹ : (Residues (p^3))ˣ)*q (g.val 1 0)
  refine ⟨r,(cubicThetaPrimeCubeCoset_eq_iff p _ _).mpr ?_⟩
  change p^3 ∣ g.val 1 0*1-g.val 1 1*(3*residueRepresentative (p^3) r)
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (g.val 1 0*1-g.val 1 1*(3*residueRepresentative (p^3) r))=0
  have hdv : (d : Residues (p^3))=q (g.val 1 1) := IsUnit.unit_spec _
  have htv : (t : Residues (p^3))=q 3 := IsUnit.unit_spec _
  have hr : q (residueRepresentative (p^3) r)=r := residueRepresentative_spec _ _
  simp only [map_sub,map_mul,mul_one]
  rw [hr,←hdv,←htv]
  change q (g.val 1 0)-(d : Residues (p^3))*
    ((t : Residues (p^3))*(((d*t)⁻¹ : (Residues (p^3))ˣ)*q (g.val 1 0)))=0
  rw [←mul_assoc,←Units.val_mul,←mul_assoc,←Units.val_mul,mul_inv_cancel,
    Units.val_one,one_mul,sub_self]

end CubicFirstMoment

end

end OAI
