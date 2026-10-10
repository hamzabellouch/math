import OAI.Combinatorics.ContingencyTables.Transport.FiniteAcceptCounts
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanStep
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanWalk

namespace OAI

/-! # Exact integer tabulation of the implemented dense bin walk -/

namespace ContingencyTables.GridBoundary
open ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseTransitionCount (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4*d^8)) : ℕ :=
  FiniteAcceptCounts.row a (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5) b

omit [DecidableEq I] [DecidableEq J] in
lemma denseTransitionCount_total (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) :
    ∑ b,denseTransitionCount R P d e a b=2^denseStepBits d := by
  have h:=FiniteAcceptCounts.row_total a
    (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5)
  simpa only [denseTransitionCount,FiniteAcceptCounts.denominator,Fintype.card_fin,
    denseStepBits,pow_add] using h

omit [DecidableEq I] [DecidableEq J] in
lemma denseTransitionCount_off_diagonal (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hq : q≤d) (e : I × J ≃ Fin q)
    (a b : Grid (I := Fin q) (4*d^8)) (hba : b≠a) :
    denseTransitionCount R P d e a b=
      if Neighbor a b then 2^(8*d^5-(denseExponent R P d e b-denseExponent R P d e a))
      else 0 := by
  simp only [denseTransitionCount,FiniteAcceptCounts.row,FiniteAcceptCounts.offCount,
    ite_eq_right hba,add_zero]
  rw [axisCodeStep_count (dense_proposal_code_bound d q hq)]
  split_ifs <;> simp

omit [DecidableEq I] [DecidableEq J] in
/-- The tabulated integer matrix is the actual Boolean step law, including
all unused proposal codes and all rejections. -/
theorem denseTransitionCount_kernel (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) :
    IntegerPropagation.kernel (denseTransitionCount R P d e) (2^denseStepBits d)
      (by positivity) (denseTransitionCount_total R P d e) a =
        denseBitStepLaw R P d e a := by
  rw [denseBitStepLaw_eq_finite]
  apply RationalLaw.eq_of_off_diagonal _ _ a
  intro b hba
  change (denseTransitionCount R P d e a b:ℚ)/((2^denseStepBits d:ℕ):ℚ)=_
  have h:=FiniteAcceptCounts.offCount_mass a b
    (fun z : Fin (2^Nat.clog 2 (8*d)) => axisCodeStep a z)
    (fun b => denseExponent R P d e b-denseExponent R P d e a) (8*d^5) hba
  simpa only [denseTransitionCount,FiniteAcceptCounts.row,ite_eq_right hba,add_zero,
    FiniteAcceptCounts.denominator,Fintype.card_fin,denseStepBits,pow_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,finiteDenseStepLaw] using h

omit [DecidableEq I] [DecidableEq J] in
/-- Matrix propagation tabulates the complete adaptive bin walk with
one integer per bin; the precision affects integer lengths, not the
number of bins enumerated. -/
theorem denseWalkCount_mass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a b : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    (IntegerPropagation.numerators (denseTransitionCount R P d e) a N b:ℚ) /
      (2:ℚ)^(N*denseStepBits d) = (denseBooleanWalkLaw R P d e a N).mass b := by
  have h:=IntegerPropagation.numerators_walkLaw (denseTransitionCount R P d e)
    (2^denseStepBits d) (by positivity) (denseTransitionCount_total R P d e) a N b
  have he : denseBooleanWalkLaw R P d e a N=
      walkLaw (denseBitStepLaw R P d e) a N := by
    unfold denseBooleanWalkLaw denseBooleanWalk
    rw [←FairBits.map_equiv (gridWordEquiv N (denseStepBits d)),FairBits.uniform_equiv]
    exact wordWalkLaw_eq _ _ _
  rw [he]
  have hk : IntegerPropagation.kernel (denseTransitionCount R P d e) (2^denseStepBits d)
      (by positivity) (denseTransitionCount_total R P d e)=denseBitStepLaw R P d e :=
    funext (denseTransitionCount_kernel R P d e)
  rw [hk] at h
  simpa only [Nat.cast_pow,Nat.cast_ofNat,←pow_mul,Nat.mul_comm (denseStepBits d) N] using h

end
end ContingencyTables.GridBoundary

end OAI
