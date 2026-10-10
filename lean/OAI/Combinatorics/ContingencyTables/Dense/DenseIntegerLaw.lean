import OAI.Combinatorics.ContingencyTables.Dense.DenseTransitionCounts
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLaw
import OAI.Combinatorics.ContingencyTables.Machines.OffsetCountProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanDraw

namespace OAI

/-! # Integer tables for the actual dense completion draw -/

namespace ContingencyTables.GridBoundary
open ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseWalkCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    IntegerLaw (Grid (I := Fin q) (4*d^8)) (2^(N*denseStepBits d)) :=
  IntegerLaw.ofMass (denseBooleanWalkLaw R P d e a N)
    (IntegerPropagation.numerators (denseTransitionCount R P d e) a N)
    (by positivity) (fun b => by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using denseWalkCount_mass R P d e a b N)

omit [DecidableEq I] [DecidableEq J] in
lemma denseWalkCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) (4*d^8)) (N : ℕ) :
    (denseWalkCounts R P d e a N).toRational (by positivity)=denseBooleanWalkLaw R P d e a N :=
  IntegerLaw.toRational_ofMass _ _ _ _

def offsetExponent (e : I × J ≃ Fin q) (w : I × J → ℕ) (h d : ℕ) : ℕ :=
  ∑ j : Fin q,offsetBitLength (w (e.symm j)) h d

def offsetCounts (e : I × J ≃ Fin q) (w : I × J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ) :
    IntegerLaw (Offset w) (2^offsetExponent e w h d) :=
  IntegerLaw.ofMass (boundedOffsetLaw e w hw h d)
    (fun o => ∏ j : Fin q,OffsetCountPrograms.offsetCount
      ((w (e.symm j),2^offsetBitLength (w (e.symm j)) h d),
        ((offsetCoordinateEquiv e w).symm o j).val)) (by positivity) (by
      intro o
      change ((∏ j : Fin q,OffsetCountPrograms.offsetCount
        ((w (e.symm j),2^offsetBitLength (w (e.symm j)) h d),
          ((offsetCoordinateEquiv e w).symm o j).val):ℕ):ℚ)/
          (2^offsetExponent e w h d:ℕ)=
        ∏ j : Fin q,(scaledLaw (w (e.symm j)) (offsetBitLength (w (e.symm j)) h d)
          (hw _)).mass ((offsetCoordinateEquiv e w).symm o j)
      simp_rw [OffsetCountPrograms.scaledLaw_mass]
      rw [Finset.prod_div_distrib,←Nat.cast_prod]
      simp only [Nat.cast_pow,Nat.cast_ofNat,offsetExponent,Finset.prod_pow_eq_pow_sum])

lemma offsetCounts_law (e : I × J ≃ Fin q) (w : I × J → ℕ) (hw : ∀ p,0<w p) (h d : ℕ) :
    (offsetCounts e w hw h d).toRational (by positivity)=boundedOffsetLaw e w hw h d :=
  IntegerLaw.toRational_ofMass _ _ _ _

def denseTrialCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    IntegerLaw (DenseTrial R P d q) (2^denseTrialBits R P d e h) :=
  ((denseWalkCounts R P d e a (d^50*(h+1)^2)).product
    (offsetCounts e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d)).rebase
      (by rw [←pow_add]; rfl)

lemma denseBooleanTrial_product (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a)=
    productLaw (denseBooleanWalkLaw R P d e a (d^50*(h+1)^2))
      (boundedOffsetLaw e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d) := by
  unfold denseBooleanTrial
  rw [←map_equiv (trialWordEquiv R P d e h)
    (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
    (fun z => (denseBooleanWalk R P d e a (d^50*(h+1)^2) z.1,
      drawOffsetWords e (integerWidth R P d) (integerWidth_pos R P d hd hR hP) h d z.2)),
    uniform_equiv,←uniform_product,mapLaw_product,drawOffsetWordsLaw_eq]
  rfl

theorem denseTrialCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (h : ℕ) (a : Grid (I := Fin q) (4*d^8)) :
    (denseTrialCounts R P d hd hR hP e h a).toRational (by positivity)=
    mapLaw (uniformLaw (α := Fin (denseTrialBits R P d e h) → Bool))
      (denseBooleanTrial R P d hd hR hP e h a) := by
  rw [denseTrialCounts,IntegerLaw.toRational_rebase,IntegerLaw.toRational_product,
    denseWalkCounts_law,offsetCounts_law,denseBooleanTrial_product] <;> positivity

def denseDrawCounts (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) :
    IntegerLaw (Table R P) (2^denseDrawBits R P d e h) :=
  (((denseTrialCounts R P d hd hR hP e h a).push (trialSuccess R P d e htotal)).retry
    fallback (d^4*(h+1))).rebase (by rw [←pow_mul,Nat.mul_comm]; rfl)

/-- Full first-success dense completion counts agree with the implemented
Boolean draw. Bin states and offset tuples are the only spaces summed. -/
theorem denseDrawCounts_law (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14≤d) (hR : ∀ i,d^12≤R i) (hP : ∀ j,d^12≤P j)
    (e : I × J ≃ Fin q) (htotal : ∑ i,R i=∑ j,P j) (h : ℕ)
    (a : Grid (I := Fin q) (4*d^8)) (fallback : Table R P) :
    (denseDrawCounts R P d hd hR hP e htotal h a fallback).toRational (by positivity)=
      denseBooleanDrawLaw R P d hd hR hP e htotal h a fallback := by
  rw [denseDrawCounts,IntegerLaw.toRational_rebase,IntegerLaw.toRational_retry,
    IntegerLaw.toRational_push,denseTrialCounts_law,retryLaw_map,retryLaw_map]
  simp only [id_eq]
  change _ = mapLaw
    (uniformLaw (α := Fin ((d^4*(h+1))*denseTrialBits R P d e h) → Bool))
    (fun bits => wordRetry
      (fun word => trialSuccess R P d e htotal (denseBooleanTrial R P d hd hR hP e h a word))
      fallback (d^4*(h+1)) (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h) bits))
  rw [←map_equiv (gridWordEquiv (d^4*(h+1)) (denseTrialBits R P d e h)),uniform_equiv]
  exact (wordRetryLaw_eq _ _ _).symm
  all_goals positivity

end
end ContingencyTables.GridBoundary

end OAI
