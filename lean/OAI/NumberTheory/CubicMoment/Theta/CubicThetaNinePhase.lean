import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryUnitResidue

namespace OAI

/-! The modulus-nine phase needed for the remaining ramified residue.
Integer multiples of three times a primary frequency lie in its kernel. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaNinePhase (h : Eisenstein) : ℂ :=
  residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)

lemma cubicThetaNinePhase_add (h k : Eisenstein) :
    cubicThetaNinePhase (h+k)=cubicThetaNinePhase h*cubicThetaNinePhase k := by
  unfold cubicThetaNinePhase
  rw [map_add,AddChar.map_add_eq_mul]

lemma cubicThetaNinePhase_three_primary {h : Eisenstein} (hh : primary h) :
    cubicThetaNinePhase (3*h)=1 := by
  have he := cubicThetaFourier_nine_triple h 1
  simp only [mul_one] at he
  unfold cubicThetaNinePhase
  rw [he,(primary_iff_residue_one h).mp hh]
  simpa only [map_one] using cubicThetaRamifiedPhase_one

lemma cubicThetaNinePhase_three_integer_primary {h : Eisenstein} (hh : primary h)
    (n : ℤ) : cubicThetaNinePhase ((n:Eisenstein)*3*h)=1 := by
  have he : (n:Eisenstein)*3*h=n • (3*h) := by simp [zsmul_eq_mul,mul_assoc]
  unfold cubicThetaNinePhase
  rw [he,map_zsmul,AddChar.map_zsmul_eq_zpow]
  change (cubicThetaNinePhase (3*h))^n=1
  rw [cubicThetaNinePhase_three_primary hh,one_zpow]

lemma cubicThetaNinePhase_eq_of_difference {h a b : Eisenstein} (hh : primary h)
    (n : ℤ) (he : a-b=(n:Eisenstein)*3*h) :
    cubicThetaNinePhase a=cubicThetaNinePhase b := by
  have hz : cubicThetaNinePhase (a-b)=1 := by
    rw [he,cubicThetaNinePhase_three_integer_primary hh]
  rw [show a=(a-b)+b by ring,cubicThetaNinePhase_add,hz,one_mul]

end CubicFirstMoment

end

end OAI
