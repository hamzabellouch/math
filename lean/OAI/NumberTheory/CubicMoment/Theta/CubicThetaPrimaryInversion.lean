import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanInversion

namespace OAI

/-! Inversion preserves exactly the primary unit classes in the finite
ring used by the actual Kloosterman kernel. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryResidue_inverse_unit (c : Eisenstein)
    (u : (Residues (3*c))ˣ) :
    cubicThetaReductionThree c (↑u⁻¹)=1 ↔ cubicThetaReductionThree c (↑u)=1 := by
  change (↑(Units.map (cubicThetaReductionThree c).toMonoidHom (u⁻¹)) : Residues 3)=1 ↔
    (↑(Units.map (cubicThetaReductionThree c).toMonoidHom u) : Residues 3)=1
  rw [Units.val_eq_one,Units.val_eq_one,map_inv,inv_eq_one]

lemma cubicThetaPrimaryResidue_inverse_perm (c : Eisenstein) (x : Residues (3*c)) :
    (IsUnit (cubicThetaResidueInversePerm (3*c) x) ∧
      cubicThetaReductionThree c (cubicThetaResidueInversePerm (3*c) x)=1) ↔
      (IsUnit x ∧ cubicThetaReductionThree c x=1) := by
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    change (IsUnit (if IsUnit (↑u : Residues (3*c)) then Ring.inverse (↑u : Residues (3*c)) else ↑u) ∧
      cubicThetaReductionThree c
        (if IsUnit (↑u : Residues (3*c)) then Ring.inverse (↑u) else ↑u)=1) ↔ _
    simp only [u.isUnit,ite_true,Ring.inverse_unit,(u⁻¹).isUnit,true_and]
    exact cubicThetaPrimaryResidue_inverse_unit c u
  · change (IsUnit (if IsUnit x then Ring.inverse x else x) ∧
      cubicThetaReductionThree c (if IsUnit x then Ring.inverse x else x)=1) ↔ _
    simp [hx]

end CubicFirstMoment

end

end OAI
