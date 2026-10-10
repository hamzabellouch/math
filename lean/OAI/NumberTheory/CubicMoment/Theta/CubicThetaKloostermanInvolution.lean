import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFinitePrimaryProjection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCharacter

namespace OAI

/-! The weighted inversion in the actual Kloosterman factorization is
self-adjoint; its square is precisely the primary-unit projection. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaResidueInversePerm_of_isUnit (q : Eisenstein) (x : Residues q)
    (hx : IsUnit x) : cubicThetaResidueInversePerm q x=Ring.inverse x := by
  change (if IsUnit x then Ring.inverse x else x)=Ring.inverse x
  exact ite_eq_left hx

lemma cubicThetaResidueInversePerm_of_not_isUnit (q : Eisenstein) (x : Residues q)
    (hx : ¬IsUnit x) : cubicThetaResidueInversePerm q x=x := by
  change (if IsUnit x then Ring.inverse x else x)=x
  exact ite_eq_right hx

lemma cubicThetaResidueInversePerm_twice (q : Eisenstein) (x : Residues q) :
    cubicThetaResidueInversePerm q (cubicThetaResidueInversePerm q x)=x := by
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    change (if IsUnit (if IsUnit (↑u : Residues q) then Ring.inverse (↑u : Residues q) else ↑u)
      then Ring.inverse (if IsUnit (↑u : Residues q) then Ring.inverse (↑u : Residues q) else ↑u)
      else (if IsUnit (↑u : Residues q) then Ring.inverse (↑u : Residues q) else ↑u))=↑u
    simp only [u.isUnit,ite_true,Ring.inverse_unit,(u⁻¹).isUnit,inv_inv]
  · change (if IsUnit (if IsUnit x then Ring.inverse x else x)
      then Ring.inverse (if IsUnit x then Ring.inverse x else x)
      else (if IsUnit x then Ring.inverse x else x))=x
    simp [hx]

lemma cubicThetaEisensteinResidueWeight_not_primary (c : Eisenstein)
    (x : Residues (3*c)) (hx : ¬(IsUnit x ∧ cubicThetaReductionThree c x=1)) :
    cubicThetaEisensteinResidueWeight c x=0 := by
  have hn : ¬(primary (residueRepresentative (3*c) x) ∧
      IsCoprime c (residueRepresentative (3*c) x)) :=
    fun he => hx ((cubicTheta_primaryResidue_iff c x).mp he)
  exact ite_eq_right hn

lemma cubicThetaEisensteinResidueWeight_one {c : Eisenstein} (hc : (3:Eisenstein)∣c) :
    cubicThetaEisensteinResidueWeight c 1=1 := by
  have he := cubicThetaEisensteinResidueWeight_mk hc 1
  simpa [cubicThetaEisensteinWeight,primary_one,cubicSymbol_one_lower,isCoprime_one_right] using he

theorem cubicThetaEisensteinResidueWeight_inverse {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (x : Residues (3*c)) :
    cubicThetaEisensteinResidueWeight c (cubicThetaResidueInversePerm (3*c) x)=
      star (cubicThetaEisensteinResidueWeight c x) := by
  by_cases hx : IsUnit x ∧ cubicThetaReductionThree c x=1
  · have hp := (cubicTheta_primaryResidue_iff c x).mpr hx
    have he := cubicThetaEisensteinResidueWeight_mul hc hp.1 hp.2
      (cubicThetaResidueInversePerm (3*c) x)
    have hi : cubicThetaResidueInversePerm (3*c) x=Ring.inverse x := by
      change (if IsUnit x then Ring.inverse x else x)=_
      rw [ite_eq_left hx.1]
    have hw : cubicThetaEisensteinResidueWeight c x=
        cubicSymbol (residueRepresentative (3*c) x) c := ite_eq_left hp
    rw [residueRepresentative_spec,hi,Ring.mul_inverse_cancel x hx.1,
      cubicThetaEisensteinResidueWeight_one hc,←hw] at he
    have hs := cubicThetaEisensteinResidueWeight_square c x
    rw [ite_eq_left hx] at hs
    have hn : cubicThetaEisensteinResidueWeight c x≠0 := by
      intro hz
      rw [hz,zero_mul] at hs
      exact zero_ne_one hs
    apply mul_left_cancel₀ hn
    rw [hi]
    exact he.symm.trans hs.symm
  · have hy : ¬(IsUnit (cubicThetaResidueInversePerm (3*c) x) ∧
        cubicThetaReductionThree c (cubicThetaResidueInversePerm (3*c) x)=1) :=
      fun hy => hx ((cubicThetaPrimaryResidue_inverse_perm c x).mp hy)
    rw [cubicThetaEisensteinResidueWeight_not_primary c x hx,
      cubicThetaEisensteinResidueWeight_not_primary c _ hy,star_zero]

theorem cubicThetaWeightedResidueInversion_square {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (f : Residues (3*c) → ℂ) (x : Residues (3*c)) :
    cubicThetaWeightedResidueInversion c (cubicThetaWeightedResidueInversion c f) x=
      cubicThetaPrimaryMultiplier c f x := by
  rw [cubicThetaWeightedResidueInversion_perm,cubicThetaWeightedResidueInversion_perm,
    cubicThetaEisensteinResidueWeight_inverse hc,cubicThetaResidueInversePerm_twice,
    ←mul_assoc,cubicThetaEisensteinResidueWeight_square]
  unfold cubicThetaPrimaryMultiplier
  split_ifs <;> simp

theorem cubicThetaWeightedResidueInversion_symmetric {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) [Fintype (Residues (3*c))]
    (f g : Residues (3*c) → ℂ) :
    (∑ x : Residues (3*c),cubicThetaWeightedResidueInversion c f x*star (g x))=
      ∑ x : Residues (3*c),f x*star (cubicThetaWeightedResidueInversion c g x) := by
  calc
    _ = ∑ x : Residues (3*c),f (cubicThetaResidueInversePerm (3*c) x)*
        star (cubicThetaWeightedResidueInversion c g (cubicThetaResidueInversePerm (3*c) x)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [cubicThetaWeightedResidueInversion_perm,cubicThetaWeightedResidueInversion_perm,
        cubicThetaEisensteinResidueWeight_inverse hc,cubicThetaResidueInversePerm_twice,
        star_mul,star_star]
      ring
    _ = _ := (cubicThetaResidueInversePerm (3*c)).sum_comp
      (fun x : Residues (3*c) => f x*star (cubicThetaWeightedResidueInversion c g x))

end CubicFirstMoment

end

end OAI
