import OAI.Analysis.PlanarPacking.MixedTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_25_10 : transformTaylor 10 25/((Nat.factorial 10):ℝ)≤(1142567497394338112201783090:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_25_11 : transformTaylor 11 25/((Nat.factorial 11):ℝ)≤(429035170759864269207836261:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_25_12 : transformTaylor 12 25/((Nat.factorial 12):ℝ)≤(147751113260532258274768477:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
