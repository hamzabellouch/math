import OAI.Analysis.PlanarPacking.CoarseTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_25_13 : sharpTaylor 13 25/((Nat.factorial 13):ℝ)≤(1709635599354057588977945053:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_14 : sharpTaylor 14 25/((Nat.factorial 14):ℝ)≤(373303454578363789549965966:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_15 : sharpTaylor 15 25/((Nat.factorial 15):ℝ)≤(76785249843842576607819054:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_16 : sharpTaylor 16 25/((Nat.factorial 16):ℝ)≤(14944038864773772626460091:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_17 : sharpTaylor 17 25/((Nat.factorial 17):ℝ)≤(2763638568673854239576766:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_18 : sharpTaylor 18 25/((Nat.factorial 18):ℝ)≤(487679883890270618281306:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_19 : sharpTaylor 19 25/((Nat.factorial 19):ℝ)≤(82459113489707738598146:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_20 : sharpTaylor 20 25/((Nat.factorial 20):ℝ)≤(13415358447817719868817:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_21 : sharpTaylor 21 25/((Nat.factorial 21):ℝ)≤(2108727150330305406116:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_22 : sharpTaylor 22 25/((Nat.factorial 22):ℝ)≤(321538539951788029867:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_23 : sharpTaylor 23 25/((Nat.factorial 23):ℝ)≤(47737694023601780598:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_24 : sharpTaylor 24 25/((Nat.factorial 24):ℝ)≤(6923525363928755660:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_25 : sharpTaylor 25 25/((Nat.factorial 25):ℝ)≤(983493777958713191:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_26 : sharpTaylor 26 25/((Nat.factorial 26):ℝ)≤(137086330848278101:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_27 : sharpTaylor 27 25/((Nat.factorial 27):ℝ)≤(18768592723534679:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_28 : sharpTaylor 28 25/((Nat.factorial 28):ℝ)≤(2524547656204976:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_29 : sharpTaylor 29 25/((Nat.factorial 29):ℝ)≤(333485942635723:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_25_30 : sharpTaylor 30 25/((Nat.factorial 30):ℝ)≤(43227396073138:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
