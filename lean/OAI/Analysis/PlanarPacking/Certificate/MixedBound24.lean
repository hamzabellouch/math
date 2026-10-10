import OAI.Analysis.PlanarPacking.MixedTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_24_12 : transformTaylor 12 24/((Nat.factorial 12):ℝ)≤(185486386187469648751994235:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_24_13 : transformTaylor 13 24/((Nat.factorial 13):ℝ)≤(58997102609725292366925614:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
