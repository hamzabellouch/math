import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFourierGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantCount

namespace OAI

/-! Exact mean-square energy of the finite Kloosterman row over its
frequency ring, with the admissible primary units counted literally. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma finite_indicator_card {α : Type*} [Finite α] (P : α → Prop) [DecidablePred P] :
    (∑' x : α,if P x then (1:ℂ) else 0)=(Nat.card {x : α // P x}:ℂ) := by
  let : Fintype α := Fintype.ofFinite α
  rw [tsum_fintype,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

lemma cubicThetaEisensteinResidueWeight_square (c : Eisenstein) (x : Residues (3*c)) :
    cubicThetaEisensteinResidueWeight c x*star (cubicThetaEisensteinResidueWeight c x)=
      if IsUnit x ∧ cubicThetaReductionThree c x=1 then 1 else 0 := by
  simp only [←cubicTheta_primaryResidue_iff]
  unfold cubicThetaEisensteinResidueWeight cubicThetaEisensteinWeight
  split_ifs with hx
  · rw [Complex.star_def,Complex.mul_conj',norm_cubicSymbol_of_isCoprime hx.1 hx.2.symm]
    norm_num
  · simp

lemma cubicThetaPrimaryResidue_indicator (c : Eisenstein) (hc0 : c≠0) :
    (∑' x : Residues (3*c),if IsUnit x ∧ cubicThetaReductionThree c x=1 then (1:ℂ) else 0)=
      (Nat.card (CubicThetaPrimaryResidue c):ℂ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  exact finite_indicator_card (fun x : Residues (3*c) => IsUnit x ∧ cubicThetaReductionThree c x=1)

theorem cubicThetaFiniteKloosterman_energy (c : Eisenstein) (hc0 : c≠0)
    (k : Residues (3*c)) :
    (∑' h : Residues (3*c),cubicThetaFiniteKloosterman c hc0 h k*
      star (cubicThetaFiniteKloosterman c hc0 h k))=
      (9*norm c:ℂ)*(Nat.card (CubicThetaPrimaryResidue c):ℂ) := by
  rw [cubicThetaFiniteKloosterman_gram,sub_self]
  simp only [zero_mul,AddChar.map_zero_eq_one,mul_one,cubicThetaEisensteinResidueWeight_square]
  rw [cubicThetaPrimaryResidue_indicator c hc0]

theorem cubicThetaFiniteKloosterman_norm_sq (c : Eisenstein) (hc0 : c≠0)
    (k : Residues (3*c)) :
    (∑' h : Residues (3*c),‖cubicThetaFiniteKloosterman c hc0 h k‖^2)=
      9*norm c*(Nat.card (CubicThetaPrimaryResidue c):ℝ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  apply Complex.ofReal_injective
  push_cast
  have he := cubicThetaFiniteKloosterman_energy c hc0 k
  simpa only [tsum_fintype,Complex.star_def,Complex.mul_conj'] using he

end CubicFirstMoment

end

end OAI
