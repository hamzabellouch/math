import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp

namespace OAI

/-! The finite residue weight used to unfold the cubic Eisenstein series.
Its modulus is exactly 3c, with zero extension outside primary coprime rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def CubicThetaBottomRow.shift (r : CubicThetaBottomRow) (m : Eisenstein) : CubicThetaBottomRow :=
  r.rightMul (cubicThetaPrincipalTranslation m)

@[simp] lemma CubicThetaBottomRow.shift_c (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).c = r.c := by
  rw [shift,rightMul_c]
  change r.c*1+r.d*0 = r.c
  ring

@[simp] lemma CubicThetaBottomRow.shift_d (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).d = r.d+3*r.c*m := by
  rw [shift,rightMul_d]
  change r.c*(3*m)+r.d*1 = r.d+3*r.c*m
  ring

@[simp] lemma CubicThetaBottomRow.shift_phase (r : CubicThetaBottomRow) (m : Eisenstein) :
    (r.shift m).phase = r.phase := by
  rw [shift,phase_rightMul,cubicThetaPrincipalTranslation_value,mul_one]

def cubicThetaEisensteinWeight (c d : Eisenstein) : ℂ :=
  if primary d ∧ IsCoprime c d then cubicSymbol d c else 0

lemma cubicThetaEisensteinWeight_periodic {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d m : Eisenstein) :
    cubicThetaEisensteinWeight c (d+3*c*m) = cubicThetaEisensteinWeight c d := by
  have hp : primary (d+3*c*m) ↔ primary d := by
    have h3 : (3:Eisenstein) ∣ 3*c*m := ⟨c*m,by ring⟩
    change (3:Eisenstein) ∣ (d+3*c*m)-1 ↔ (3:Eisenstein) ∣ d-1
    rw [show (d+3*c*m)-1 = (d-1)+3*c*m by ring]
    simpa only [add_comm] using (dvd_add_right h3 :
      (3:Eisenstein) ∣ 3*c*m+(d-1) ↔ (3:Eisenstein) ∣ d-1)
  have hg : IsCoprime c (d+3*c*m) ↔ IsCoprime c d := by
    rw [show d+3*c*m = d+c*(3*m) by ring]
    exact IsCoprime.add_mul_left_right_iff
  unfold cubicThetaEisensteinWeight
  rw [hp,hg]
  split_ifs with hd
  · let r : CubicThetaBottomRow := ⟨c,d,hc,hd.1,hd.2⟩
    have he := congrArg star (r.shift_phase m)
    simpa only [CubicThetaBottomRow.phase,CubicThetaBottomRow.shift_c,
      CubicThetaBottomRow.shift_d,star_star] using he
  · rfl

def cubicThetaEisensteinResidueWeight (c : Eisenstein) (x : Residues (3*c)) : ℂ :=
  cubicThetaEisensteinWeight c (residueRepresentative (3*c) x)

lemma cubicThetaEisensteinResidueWeight_mk {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d : Eisenstein) :
    cubicThetaEisensteinResidueWeight c (Ideal.Quotient.mk (modulus (3*c)) d) =
      cubicThetaEisensteinWeight c d := by
  let r := residueRepresentative (3*c) (Ideal.Quotient.mk (modulus (3*c)) d)
  have hd : (3*c) ∣ r-d := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    change Ideal.Quotient.mk (modulus (3*c)) r-Ideal.Quotient.mk (modulus (3*c)) d = 0
    rw [residueRepresentative_spec,sub_self]
  obtain ⟨m,hm⟩ := hd
  change cubicThetaEisensteinWeight c r = _
  rw [show r = d+3*c*m by linear_combination hm]
  exact cubicThetaEisensteinWeight_periodic hc d m

end CubicFirstMoment

end

end OAI
