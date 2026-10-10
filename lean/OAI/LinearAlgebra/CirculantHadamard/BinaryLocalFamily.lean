import OAI.LinearAlgebra.CirculantHadamard.BinaryLocalRing
import OAI.LinearAlgebra.CirculantHadamard.BinaryProductTransport
import OAI.LinearAlgebra.CirculantHadamard.BinaryCharacterSum
import OAI.LinearAlgebra.CirculantHadamard.BinaryResidue

namespace OAI

noncomputable section

namespace CirculantHadamard.BinaryLocalFamily

open scoped BigOperators
open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing
open BinaryLocalRing BinaryProductTransport

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u) (hodd : Odd u)

/-- The actual local unit attached to one evaluated Gaussian norm element. -/
def evaluationUnit (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) : (O u)ˣ :=
  normUnit u hodd (subsetEvaluation u hu S x) (star (subsetEvaluation u hu S x))
    (by simpa only [Nat.cast_pow] using subsetEvaluation_norm u hu S x hx)

@[simp] theorem evaluationUnit_val (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (S : Finset (PrimeIndex u)) :
    (evaluationUnit u hu hodd x hx S : O u) = toLocal u (subsetEvaluation u hu S x) :=
  normUnit_val _ _ _ _ _

include hodd in
/-- The concrete local argument. In particular, neither local units nor a
nonzero residue sum are assumptions of this theorem. -/
theorem contradiction_of_evaluated_data
    (C D G : Elem GaussianRing (u ^ 2))
    (hC : C * ringStar C = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hD : D * ringStar D = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (hG : G * ringStar G = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (a b U : Finset (PrimeIndex u) → B u)
    (hc : ∀ S, subsetEvaluation u hu S C = a S + b S)
    (hd : ∀ S, subsetEvaluation u hu S D = a S - b S)
    (hg : ∀ S, subsetEvaluation u hu S G =
      a S + gaussianToB u gaussianI * b S -
        ((1 + gaussianToB u gaussianI) *
          subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing)) + 2 * U S))
    (hCodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S C))) ^ m = 1)
    (hDodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S D))) ^ m = 1)
    (hGodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S G))) ^ m = 1) :
    False := by
  classical
  let c := evaluationUnit u hu hodd C hC
  let d := evaluationUnit u hu hodd D hD
  let g := evaluationUnit u hu hodd G hG
  have cval (S) : (c S : O u) = toLocal u (subsetEvaluation u hu S C) :=
    evaluationUnit_val u hu hodd C hC S
  have dval (S) : (d S : O u) = toLocal u (subsetEvaluation u hu S D) :=
    evaluationUnit_val u hu hodd D hD S
  have gval (S) : (g S : O u) = toLocal u (subsetEvaluation u hu S G) :=
    evaluationUnit_val u hu hodd G hG S
  have hr := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S D) (fun S => subsetEvaluation u hu S C)
    d c (fun S _ => dval S) (fun S _ => cval S) hDodd hCodd
  have hw := local_alternatingProduct_ratio_has_odd_power u Finset.univ
    (fun S => subsetEvaluation u hu S G) (fun S => subsetEvaluation u hu S C)
    g c (fun S _ => gval S) (fun S _ => cval S) hGodd hCodd
  apply binary_residue_contradiction (residue u) (imaginary u)
    (imaginary_sq u) (residue_imaginary u) (two_ne_zero u)
    (Finset.univ : Finset (Finset (PrimeIndex u))) subsetSign c d g
    (fun S => toLocal u (a S)) (fun S => toLocal u (b S))
    (fun S => toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))))
    (fun S => toLocal u (U S))
  · intro S _
    rw [cval, hc, map_add]
  · intro S _
    rw [dval, hd, map_sub]
  · intro S _
    rw [gval, hg]
    have hi_local : toLocal u (gaussianToB u gaussianI) = imaginary u := by
      change toLocal u ((gaussianToB u).toRingHom gaussianI) =
        ((toLocal u).comp (gaussianToB u).toRingHom) gaussianI
      exact (RingHom.comp_apply _ _ _).symm
    simp only [map_sub, map_add, map_mul, map_one, map_ofNat, hi_local]
  · simpa only [alternatingProduct, Finset.powerset_univ] using hr
  · simpa only [alternatingProduct, Finset.powerset_univ] using hw
  · have hnonzero := BinaryCharacterSum.actual_subset_J_residue_ne_zero u hu
      (toLocal u) (residue u) (fun S => (↑((c S)⁻¹) : O u)) (c ∅) rfl hodd
    have hsum : (residue u)
        (∑ S : Finset (PrimeIndex u), (subsetSign S : O u) *
          toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
            (↑((c S)⁻¹) : O u)) =
        ∑ S : Finset (PrimeIndex u), (residue u)
          ((subsetSign S : O u) *
            toLocal u (subsetEvaluation u hu S (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver GaussianRing))) *
              (↑((c S)⁻¹) : O u)) :=
      map_sum (residue u).toAddMonoidHom _ _
    rw [hsum] at hnonzero
    simpa only [map_mul, map_intCast, mul_assoc] using hnonzero

end CirculantHadamard.BinaryLocalFamily

end

end OAI
