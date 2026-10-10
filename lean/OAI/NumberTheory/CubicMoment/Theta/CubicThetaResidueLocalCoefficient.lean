import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInverseResidues
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAveragedVoronoi

namespace OAI

/-! The concrete finite dual cusp coefficient equals the universal
three-cusp coefficient times the exact local Ramanujan product. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

theorem cubicThetaResidueDualCoefficient_local {r : Eisenstein} (hr : primary r)
    (hs : Squarefree r) [Fintype (Residues r)] (n : MetaplecticDualArgument) :
    cubicThetaResidueDualCoefficient r hr n.val=
      cubicThetaCommonCuspCoefficient n.val*metaplecticLocalCoefficient r n := by
  let F (x : Residues r) : ℂ := cubicSymbol r (residueRepresentative r x)*
    cubicThetaCoefficientTwist
      (cubicThetaProjectedCoefficient (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))
        (cubicThetaResidueCuspPrimary r hr (residueRepresentative r x)))
      (cubicThetaPrimaryDualCenter (cubicThetaResidueCuspMatrix r hr (residueRepresentative r x))) n.val
  have hz (x : Residues r) (hx : ¬IsUnit x) : F x=0 := by
    have hn : ¬IsCoprime r (residueRepresentative r x) := by
      intro h
      exact hx (by simpa only [residueRepresentative_spec] using residue_isUnit_of_isCoprime h)
    dsimp only [F]
    rw [cubicSymbol_eq_zero_of_not_isCoprime hr hn,zero_mul]
  have ht (u : (Residues r)ˣ) : F u=
      cubicThetaCommonCuspCoefficient n.val*
        additivePhase r (-n.val*cubicThetaNineUnitInverse r hr u) := by
    have hu := cubicThetaUnitRepresentative_coprime r u
    have hg := cubicThetaResidueCuspMatrix_of_coprime r hr _ hu
    have ha := cubicThetaProjectedCoefficient_congr hg
      (cubicThetaResidueCuspPrimary r hr _) (cubicThetaNineGaussMatrix_primary r hr _ hu)
    have hz := congrArg cubicThetaPrimaryDualCenter hg
    dsimp only [F,cubicThetaCoefficientTwist]
    rw [ha,hz]
    have H := cubicThetaNineGaussMatrix_weighted_coefficient r hr (residueRepresentative r u) hu
      (cubicThetaNineUnitInverse r hr u) (cubicThetaNineUnitInverse_spec r hr u) n.val
    exact H
  change (∑ x : Residues r,F x)=_
  rw [cubicTheta_sum_eq_units F hz]
  simp_rw [ht]
  rw [←Finset.mul_sum,cubicThetaNineUnitInverse_average,cubicThetaRamanujan_squarefree hr hs]

end CubicFirstMoment

end

end OAI
