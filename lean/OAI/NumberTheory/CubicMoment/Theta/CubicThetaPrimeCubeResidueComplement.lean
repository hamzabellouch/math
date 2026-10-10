import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueStep

namespace OAI

/-! The unit and complementary chart parameters exhaust the residue
ring modulo p^3 without overlap or multiplicity. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeResidueComplement_sum {p : Eisenstein} (hp : primaryPrime p)
    (f : Residues (p^3) → ℂ) :
    (∑' r : Residues (p^3), f r)=
      (∑' u : (Residues (p^3))ˣ, f u)+
      ∑' r : cubicThetaPrimeCubeUpperParameter p, f r.val := by
  classical
  let : Finite (Residues (p^3)) := finite_residues (pow_ne_zero 3 hp.2.ne_zero)
  let : Finite (cubicThetaPrimeCubeUpperParameter p) := by
    unfold cubicThetaPrimeCubeUpperParameter
    infer_instance
  let e : cubicThetaPrimeCubeUpperParameter p ≃ {r : Residues (p^3) // ¬IsUnit r} :=
    Equiv.subtypeEquivRight (fun r => ((cubicTheta_primePower_nonunit_iff hp.2 2 r).trans
      (cubicTheta_residueReduction_eq_zero_iff _ r)).symm)
  let E : ((Residues (p^3))ˣ ⊕ cubicThetaPrimeCubeUpperParameter p) ≃ Residues (p^3) :=
    (Equiv.sumCongr (cubicThetaUnitsEquivIsUnit _) e).trans (Equiv.sumCompl IsUnit)
  rw [←E.tsum_eq,Summable.tsum_sum Summable.of_finite Summable.of_finite]
  rfl

end CubicFirstMoment

end

end OAI
