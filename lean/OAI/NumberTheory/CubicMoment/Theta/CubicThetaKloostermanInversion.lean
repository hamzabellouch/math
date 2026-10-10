import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFourierGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCount

namespace OAI

/-! Inversion on the actual unit residues and the contraction supplied by
the cubic weight with its common-factor zero extension. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaResidueInversePerm (q : Eisenstein) : Residues q ≃ Residues q :=
  Function.Involutive.toPerm (f:=fun x : Residues q => if IsUnit x then Ring.inverse x else x) (by
    intro x
    by_cases hx : IsUnit x
    · obtain ⟨u,rfl⟩ := hx
      simp [u.isUnit,(u⁻¹).isUnit]
    · simp [hx])

lemma cubicThetaEisensteinResidueWeight_nonunit (c : Eisenstein) (x : Residues (3*c))
    (hx : ¬IsUnit x) : cubicThetaEisensteinResidueWeight c x=0 := by
  have hn : ¬(primary (residueRepresentative (3*c) x) ∧
      IsCoprime c (residueRepresentative (3*c) x)) := by
    intro he
    exact hx ((cubicTheta_primaryResidue_iff c x).mp he).1
  simp only [cubicThetaEisensteinResidueWeight,cubicThetaEisensteinWeight,ite_eq_right hn]

def cubicThetaWeightedResidueInversion (c : Eisenstein)
    (f : Residues (3*c) → ℂ) (x : Residues (3*c)) : ℂ :=
  cubicThetaEisensteinResidueWeight c x*f (Ring.inverse x)

lemma cubicThetaWeightedResidueInversion_perm (c : Eisenstein)
    (f : Residues (3*c) → ℂ) (x : Residues (3*c)) :
    cubicThetaWeightedResidueInversion c f x=
      cubicThetaEisensteinResidueWeight c x*f (cubicThetaResidueInversePerm (3*c) x) := by
  by_cases hx : IsUnit x
  · change cubicThetaEisensteinResidueWeight c x*f (Ring.inverse x)=
      cubicThetaEisensteinResidueWeight c x*f (if IsUnit x then Ring.inverse x else x)
    rw [ite_eq_left hx]
  · simp [cubicThetaWeightedResidueInversion,cubicThetaEisensteinResidueWeight_nonunit c x hx]

theorem cubicThetaWeightedResidueInversion_contract (c : Eisenstein)
    [Fintype (Residues (3*c))] (f : Residues (3*c) → ℂ) :
    (∑ x : Residues (3*c),‖cubicThetaWeightedResidueInversion c f x‖^2)≤
      ∑ x : Residues (3*c),‖f x‖^2 := by
  calc
    _ ≤ ∑ x : Residues (3*c),‖f (cubicThetaResidueInversePerm (3*c) x)‖^2 := by
      apply Finset.sum_le_sum
      intro x _
      rw [cubicThetaWeightedResidueInversion_perm,norm_mul]
      apply pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
      exact (mul_le_mul_of_nonneg_right (cubicThetaEisensteinWeight_norm c _)
        (_root_.norm_nonneg _)).trans_eq (one_mul _)
    _ = _ := (cubicThetaResidueInversePerm (3*c)).sum_comp (fun x => ‖f x‖^2)

end CubicFirstMoment

end

end OAI
