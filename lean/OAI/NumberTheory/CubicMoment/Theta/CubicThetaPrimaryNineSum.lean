import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryResidueNine

namespace OAI

/-! Finite summation on the primary coset modulo nine. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaPrimaryNine_sum (f : Residues (9:Eisenstein) → ℂ) :
    (∑' x : Residues (9:Eisenstein),
      if primary (residueRepresentative 9 x) then f x else 0)=
    ∑' y : Residues (3:Eisenstein), f (cubicThetaPrimaryNineLift y).val := by
  classical
  let : Finite (Residues (9:Eisenstein)) := finite_residues (by norm_num)
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (9:Eisenstein)) := Fintype.ofFinite _
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_subtype (p:=fun x : Residues (9:Eisenstein) =>
      primary (residueRepresentative 9 x)) _ (by simp) f]
  exact (Equiv.sum_comp cubicThetaPrimaryNineEquiv (fun x => f x.val)).symm

lemma cubicThetaPrimaryNineLift_character (y : Residues (3:Eisenstein)) :
    cubicSymbol (residueRepresentative 9 (cubicThetaPrimaryNineLift y).val) lambdaE=
      cubicThetaRamifiedCharacter (residueRepresentative 3 y) := by
  apply cubicSymbol_lambda_periodic (cubicThetaPrimaryNineLift y).property
    (show primary (1+3*residueRepresentative 3 y) from ⟨_,by ring⟩)
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr (residueRepresentative_spec 9 (cubicThetaPrimaryNineLift y).val)

end CubicFirstMoment

end

end OAI
