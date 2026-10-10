import OAI.Analysis.PlanarPacking.CoarseTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_39_13 : sharpTaylor 13 39/((Nat.factorial 13):ℝ)≤(1664852226480760855251115215:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_14 : sharpTaylor 14 39/((Nat.factorial 14):ℝ)≤(360072405296350561646305502:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_15 : sharpTaylor 15 39/((Nat.factorial 15):ℝ)≤(73135605280913779366227181:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_16 : sharpTaylor 16 39/((Nat.factorial 16):ℝ)≤(13999972081593772060522585:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_17 : sharpTaylor 17 39/((Nat.factorial 17):ℝ)≤(2533740559077991082380588:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_18 : sharpTaylor 18 39/((Nat.factorial 18):ℝ)≤(434793971241399101497012:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_19 : sharpTaylor 19 39/((Nat.factorial 19):ℝ)≤(70931275596672662697091:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_20 : sharpTaylor 20 39/((Nat.factorial 20):ℝ)≤(11027804147365847283637:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_21 : sharpTaylor 21 39/((Nat.factorial 21):ℝ)≤(1637712529509843641519:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_22 : sharpTaylor 22 39/((Nat.factorial 22):ℝ)≤(232829180807700478412:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_23 : sharpTaylor 23 39/((Nat.factorial 23):ℝ)≤(31755000489523633449:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_24 : sharpTaylor 24 39/((Nat.factorial 24):ℝ)≤(4163634013653937202:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_25 : sharpTaylor 25 39/((Nat.factorial 25):ℝ)≤(525936767355968363:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_26 : sharpTaylor 26 39/((Nat.factorial 26):ℝ)≤(64140423352441557:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_27 : sharpTaylor 27 39/((Nat.factorial 27):ℝ)≤(7569093846066644:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_28 : sharpTaylor 28 39/((Nat.factorial 28):ℝ)≤(866368337543320:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_29 : sharpTaylor 29 39/((Nat.factorial 29):ℝ)≤(96429547209064:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_39_30 : sharpTaylor 30 39/((Nat.factorial 30):ℝ)≤(10465115562657:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
