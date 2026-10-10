import OAI.Analysis.PlanarPacking.MixedTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_40_4 : transformTaylor 4 40/((Nat.factorial 4):ℝ)≤(1378005254342885432796058460:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_5 : transformTaylor 5 40/((Nat.factorial 5):ℝ)≤(1127662331737765183970897290:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_6 : transformTaylor 6 40/((Nat.factorial 6):ℝ)≤(770206922867263530745282246:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_7 : transformTaylor 7 40/((Nat.factorial 7):ℝ)≤(451541240469518315478157760:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_8 : transformTaylor 8 40/((Nat.factorial 8):ℝ)≤(231919502450331624380412515:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_9 : transformTaylor 9 40/((Nat.factorial 9):ℝ)≤(105999991106160182956535889:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_10 : transformTaylor 10 40/((Nat.factorial 10):ℝ)≤(43645893453395484376071552:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_11 : transformTaylor 11 40/((Nat.factorial 11):ℝ)≤(16351797364128125134540904:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_12 : transformTaylor 12 40/((Nat.factorial 12):ℝ)≤(5619945822412676134103778:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_40_13 : transformTaylor 13 40/((Nat.factorial 13):ℝ)≤(1784145647367326687478989:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
