import OAI.Analysis.PlanarPacking.CoarseTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_40_14 : sharpTaylor 14 40/((Nat.factorial 14):ℝ)≤(359948030220811358468508434:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_15 : sharpTaylor 15 40/((Nat.factorial 15):ℝ)≤(73101330640895937061956764:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_16 : sharpTaylor 16 40/((Nat.factorial 16):ℝ)≤(13991113615257622005778749:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_17 : sharpTaylor 17 40/((Nat.factorial 17):ℝ)≤(2531584957295558794531248:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_18 : sharpTaylor 18 40/((Nat.factorial 18):ℝ)≤(434298419192079078824557:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_19 : sharpTaylor 19 40/((Nat.factorial 19):ℝ)≤(70823319651958197945600:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_20 : sharpTaylor 20 40/((Nat.factorial 20):ℝ)≤(11005456571581433577095:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_21 : sharpTaylor 21 40/((Nat.factorial 21):ℝ)≤(1633305813580668845433:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_22 : sharpTaylor 22 40/((Nat.factorial 22):ℝ)≤(231999568704594068604:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_23 : sharpTaylor 23 40/((Nat.factorial 23):ℝ)≤(31605583903391060769:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_24 : sharpTaylor 24 40/((Nat.factorial 24):ℝ)≤(4137841164878736335:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_25 : sharpTaylor 25 40/((Nat.factorial 25):ℝ)≤(521661890364323678:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_26 : sharpTaylor 26 40/((Nat.factorial 26):ℝ)≤(63459088639384934:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_27 : sharpTaylor 27 40/((Nat.factorial 27):ℝ)≤(7464514217057929:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_28 : sharpTaylor 28 40/((Nat.factorial 28):ℝ)≤(850888213873540:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_29 : sharpTaylor 29 40/((Nat.factorial 29):ℝ)≤(94217000959864:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_40_30 : sharpTaylor 30 40/((Nat.factorial 30):ℝ)≤(10159402696372:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
