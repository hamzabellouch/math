import OAI.Analysis.PlanarPacking.RationalBounds

namespace OAI

/-!
# Scalar sign margins

Rational bounds for coefficient perturbations and Taylor remainders on half-gaps.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma perturbation_zero_cap : (3:ℝ)/10^5*(directRational 0+transformRational 0 0)<4/1000 := by
  norm_num [directRational,transformRational,pieceIntCap,massRational,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,slopeCap,zCap,Fin.sum_univ_succ]
lemma perturbation_one_cap : (3:ℝ)/10^5*(directRational 1+halfTransform 1)<11/1000 := by
  norm_num [directRational,halfTransform,halfCap,halfBase,halfMass,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,slopeCap,zCap,Fin.sum_univ_succ]
lemma perturbation_two_cap : (3:ℝ)/10^5*(directRational 2+halfTransform 2)/2<11/1000 := by
  norm_num [directRational,halfTransform,halfCap,halfBase,halfMass,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,slopeCap,zCap,Fin.sum_univ_succ]
lemma perturbation_large_cap : (3:ℝ)/10^5*(directRational 2+transformRational 2 2)/2<2/1000 := by
  norm_num [directRational,transformRational,pieceIntCap,massRational,piUpper,
    densityCap,densityNum,densityDen,lambdaCap,pieceBase,slopeCap,zCap,Fin.sum_univ_succ]
lemma taylor_cap0 : taylorEnvelope 29 0*(1/2:ℝ)^29/((29 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap1 : taylorEnvelope 31 0*(1/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap2 : taylorEnvelope 30 1*(1:ℝ)^29/((30 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap3 : taylorEnvelope 31 1*(1:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap4 : taylorEnvelope 31 2*(1:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap5 : taylorEnvelope 31 3*(1/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap6 : taylorEnvelope 31 4*(3/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma taylor_cap7 : taylorEnvelope 31 5*(3/2:ℝ)^29/((31 : ℕ).factorial:ℝ)<1/1000 := by
  norm_num [taylorEnvelope,transformRational,atomicRational,pieceIntCap,atomIntCap,
    massRational,piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,
    atomMass,atomBase,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
