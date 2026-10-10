import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUnitPhaseSymbol

namespace OAI

/-! Conjugation preserves the exact arithmetic coefficient coordinates,
including their ramified exponent and unit phase. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNinePhase_conjugate (n : Eisenstein) :
    cubicThetaNinePhase (conjugate n) = star (cubicThetaNinePhase n) := by
  obtain ⟨a,b,hn⟩ := exists_coordinates n
  have he : n = ofCoords a b := Subtype.ext (by simpa only [ofCoords_coe] using hn)
  have hc : conjugate n = ofCoords (a-b) (-b) := by
    apply Subtype.ext
    rw [conjugate_coe,hn]
    simp only [star_add,star_mul,star_intCast,star_omega_linear,ofCoords_coe]
    push_cast
    ring
  rw [hc,he,cubicThetaNinePhase_coordinates,cubicThetaNinePhase_coordinates]
  simp only [Int.cast_neg,neg_div,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,
    Complex.star_def]

lemma cubicThetaUnitPhase_fourth {u v : Eisensteinˣ}
    (h : (u:Eisenstein)^4 = (v:Eisenstein)^4) :
    cubicThetaUnitPhase u = cubicThetaUnitPhase v := by
  simp only [cubicThetaUnitPhase,h]

@[simp] lemma cubicTheta_conjugateUnit_val (u : Eisensteinˣ) :
    ((Units.map conjugate.toMonoidHom u):Eisenstein) = conjugate (u:Eisenstein) := rfl

lemma cubicThetaUnitPhase_conjugate (u : Eisensteinˣ) :
    cubicThetaUnitPhase (Units.map conjugate.toMonoidHom u) =
      star (cubicThetaUnitPhase u) := by
  rw [cubicThetaUnitPhase_eq,cubicThetaUnitPhase_eq]
  simpa only [cubicTheta_conjugateUnit_val,←map_pow] using
    cubicThetaNinePhase_conjugate ((u:Eisenstein)^2)

def CubicThetaCoordinates.conjugated {n : Eisenstein} (R : CubicThetaCoordinates n) :
    CubicThetaCoordinates (conjugate n) where
  unit := Units.map conjugate.toMonoidHom R.unit * (-1)^R.order
  order := R.order
  squarefreePart := conjugate R.squarefreePart
  cubePart := conjugate R.cubePart
  squarefree_primary := primary_conjugate R.squarefree_primary
  cube_primary := primary_conjugate R.cube_primary
  squarefree := cubicTheta_squarefree_conjugate R.squarefree
  numerator_eq := by
    conv_lhs => rw [R.numerator_eq]
    rw [map_mul,map_mul,map_mul,map_pow,map_pow,cubicTheta_conjugate_lambda]
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one]
    rw [neg_eq_neg_one_mul,mul_pow]
    ring

lemma CubicThetaCoordinates.conjugated_amplitude {n : Eisenstein}
    (R : CubicThetaCoordinates n) : R.conjugated.amplitude = R.amplitude := by
  simp only [amplitude,conjugated,norm_conjugate]

lemma CubicThetaCoordinates.conjugated_unit_fourth {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    (R.conjugated.unit:Eisenstein)^4 = conjugate ((R.unit:Eisenstein)^4) := by
  simp only [conjugated,Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one,mul_pow,←pow_mul]
  rw [Nat.mul_comm R.order 4,pow_mul]
  norm_num [map_pow]

lemma CubicThetaCoordinates.conjugated_phase {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    cubicThetaUnitPhase R.conjugated.unit = star (cubicThetaUnitPhase R.unit) := by
  rw [cubicThetaUnitPhase_fourth (v := Units.map conjugate.toMonoidHom R.unit)
    (by simpa only [cubicTheta_conjugateUnit_val,map_pow] using R.conjugated_unit_fourth)]
  exact cubicThetaUnitPhase_conjugate R.unit

end CubicFirstMoment

end

end OAI
