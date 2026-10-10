import OAI.Analysis.PlanarPacking.MixedTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_39_6 : transformTaylor 6 39/((Nat.factorial 6):ℝ)≤(950984512557742813967069481:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_7 : transformTaylor 7 39/((Nat.factorial 7):ℝ)≤(557658605426100677627684034:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_8 : transformTaylor 8 39/((Nat.factorial 8):ℝ)≤(286484792976969139723090417:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_9 : transformTaylor 9 39/((Nat.factorial 9):ℝ)≤(130964293330677630666136863:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_10 : transformTaylor 10 39/((Nat.factorial 10):ℝ)≤(53934136505805891769016377:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_11 : transformTaylor 11 39/((Nat.factorial 11):ℝ)≤(20209267537129097201365382:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma mixed_39_12 : transformTaylor 12 39/((Nat.factorial 12):ℝ)≤(6946632271962133634215599:ℝ)/1000000000000000000000000000000 := by
  norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
