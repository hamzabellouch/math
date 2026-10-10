import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanNormalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFiniteFourier

namespace OAI

/-! The completion coordinate in the row phase is exactly the inverse
of the lower-right entry modulo 3c. This removes its choice from the finite sum. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRowResidueUnit (r : CubicThetaBottomRow) : (Residues (3*r.c))ˣ :=
  (residue_isUnit_of_isCoprime ((primary_coprime_three r.d_primary).symm.mul_left r.coprime)).unit

lemma cubicThetaRowResidueUnit_val (r : CubicThetaBottomRow) :
    (cubicThetaRowResidueUnit r : Residues (3*r.c))=
      Ideal.Quotient.mk (modulus (3*r.c)) r.d := IsUnit.unit_spec _

lemma cubicThetaRow_completion_inverse (r : CubicThetaBottomRow) :
    Ideal.Quotient.mk (modulus (3*r.c)) (r.completion.val 0 0)=
      ((cubicThetaRowResidueUnit r)⁻¹ : (Residues (3*r.c))ˣ) := by
  let q := Ideal.Quotient.mk (modulus (3*r.c))
  have hd : r.completion.val 1 1=r.d := congrArg CubicThetaBottomRow.d r.completion_row
  have hc : r.completion.val 1 0=r.c := congrArg CubicThetaBottomRow.c r.completion_row
  have hdet := cubicThetaPrincipalGroup_det r.completion
  rw [hd,hc] at hdet
  obtain ⟨b,hb⟩ := (cubicThetaPrincipalGroup_offDiagonal r.completion).1
  have hdiv : 3*r.c∣r.completion.val 0 0*r.d-1 := by
    refine ⟨b,?_⟩
    rw [hb] at hdet
    linear_combination hdet
  have hmul : q (r.completion.val 0 0)*(cubicThetaRowResidueUnit r:Residues (3*r.c))=1 := by
    rw [cubicThetaRowResidueUnit_val,←map_mul]
    exact (residue_eq_of_dvd_sub hdiv).trans (map_one q)
  calc
    _ = q (r.completion.val 0 0)*((cubicThetaRowResidueUnit r:Residues (3*r.c))*
        (((cubicThetaRowResidueUnit r)⁻¹:(Residues (3*r.c))ˣ):Residues (3*r.c))) := by
      rw [←Units.val_mul,mul_inv_cancel,Units.val_one,mul_one]
    _ = _ := by rw [←mul_assoc,hmul,one_mul]

lemma cubicThetaHorizontalCharacter_residue {c : Eisenstein} (hc : c≠0)
    (h d : Eisenstein) :
    cubicThetaHorizontalCharacter h ((d:ℂ)/(c:ℂ))=
      residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
        (Ideal.Quotient.mk (modulus (3*c)) (h*d)) := by
  have he : (d:ℂ)/(c:ℂ)=3*(d:ℂ)/((3*c:Eisenstein):ℂ) := by
    rw [Subalgebra.coe_mul,show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
    have hcC : (c:ℂ)≠0 := fun hz => hc (Subtype.ext hz)
    field_simp
  rw [he,cubicThetaHorizontalCharacter_fraction]

theorem cubicThetaGramRowPhase_residue (h k : Eisenstein)
    (r : CubicThetaBottomRow) (hr : r.c≠0) :
    cubicThetaGramRowPhase h k r=cubicSymbol r.d r.c*
      residueFourierChar (3*r.c) (mul_ne_zero (by norm_num) hr)
        (Ideal.Quotient.mk (modulus (3*r.c)) h*(cubicThetaRowResidueUnit r:Residues (3*r.c))+
         Ideal.Quotient.mk (modulus (3*r.c)) k*
          (((cubicThetaRowResidueUnit r)⁻¹:(Residues (3*r.c))ˣ):Residues (3*r.c))) := by
  rw [cubicThetaGramRowPhase,CubicThetaBottomRow.phase,star_star,
    cubicThetaHorizontalCharacter_residue hr,cubicThetaHorizontalCharacter_residue hr,
    map_mul (Ideal.Quotient.mk (modulus (3*r.c))) h r.d,
    map_mul (Ideal.Quotient.mk (modulus (3*r.c))) k (r.completion.val 0 0),
    ←cubicThetaRowResidueUnit_val,cubicThetaRow_completion_inverse,
    AddChar.map_add_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
