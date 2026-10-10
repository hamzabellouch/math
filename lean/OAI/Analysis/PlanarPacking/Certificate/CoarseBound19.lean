import OAI.Analysis.PlanarPacking.CoarseTaylor

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_19_14 : sharpTaylor 14 19/((Nat.factorial 14):ℝ)≤(415519823301646288216618079:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_15 : sharpTaylor 15 19/((Nat.factorial 15):ℝ)≤(88441022552632104701542875:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_16 : sharpTaylor 16 19/((Nat.factorial 16):ℝ)≤(17961769109023805605644033:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_17 : sharpTaylor 17 19/((Nat.factorial 17):ℝ)≤(3499152986883578905581056:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_18 : sharpTaylor 18 19/((Nat.factorial 18):ℝ)≤(657025204371517831247787:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_19 : sharpTaylor 19 19/((Nat.factorial 19):ℝ)≤(119404930671123464551117:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_20 : sharpTaylor 20 19/((Nat.factorial 20):ℝ)≤(21074327843674396260647:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_21 : sharpTaylor 21 19/((Nat.factorial 21):ℝ)≤(3621158106959460131472:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_22 : sharpTaylor 22 19/((Nat.factorial 22):ℝ)≤(606685585115109330584:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_23 : sharpTaylor 23 19/((Nat.factorial 23):ℝ)≤(99171959366183814819:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_24 : sharpTaylor 24 19/((Nat.factorial 24):ℝ)≤(15816651699858251513:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_25 : sharpTaylor 25 19/((Nat.factorial 25):ℝ)≤(2460008358849052878:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_26 : sharpTaylor 26 19/((Nat.factorial 26):ℝ)≤(372867321116342342:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_27 : sharpTaylor 27 19/((Nat.factorial 27):ℝ)≤(55036650600723914:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_28 : sharpTaylor 28 19/((Nat.factorial 28):ℝ)≤(7905972890555824:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_29 : sharpTaylor 29 19/((Nat.factorial 29):ℝ)≤(1104748937734647:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_19_30 : sharpTaylor 30 19/((Nat.factorial 30):ℝ)≤(150128174659659:ℝ)/1000000000000000000000000000000 := by
  norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
