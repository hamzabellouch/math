import OAI.Analysis.PlanarPacking.MixedTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_27_10 : transformTaylor 10 27/((Nat.factorial 10):ℝ)≤(728815928958878777357237282:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_27_11 : transformTaylor 11 27/((Nat.factorial 11):ℝ)≤(273586055473683921267866222:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_27_12 : transformTaylor 12 27/((Nat.factorial 12):ℝ)≤(94191747073031887938338274:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
