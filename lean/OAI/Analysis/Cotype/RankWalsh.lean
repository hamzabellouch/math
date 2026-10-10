import OAI.Analysis.Cotype.TaggedCoefficient
import OAI.Analysis.Cotype.RankFactors
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {m r k : ℕ}

theorem character_binary_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P s : ι → Bool) :
    character P s = binarySign (∑ i, binaryBit (P i) * binaryBit (s i)) := by
  rw [binarySign_sum]
  apply Finset.prod_congr rfl
  intro i hi
  cases P i <;> cases s i <;> simp [binaryBit, sign]

def blockCoordinates (ζ : Cube (r*k)) (p : Fin k) : Fin r → ZMod 2 :=
  fun l => binaryBit (ζ (finProdFinEquiv (l,p)))

def rankSubstitute (I : Matrix (Fin m) (Fin r) (ZMod 2)) (ζ : Cube (r*k)) : Fin m → Cube k :=
  fun i => (cubeBinaryEquiv k).symm (fun p => I.mulVec (blockCoordinates ζ p) i)

@[simp] theorem rankSubstitute_bit (I : Matrix (Fin m) (Fin r) (ZMod 2)) (ζ : Cube (r*k))
    (i : Fin m) (p : Fin k) :
    binaryBit (rankSubstitute I ζ i p) = I.mulVec (blockCoordinates ζ p) i :=
  congrFun ((cubeBinaryEquiv k).apply_symm_apply _) p

theorem rankSubstitute_character (P : SignMatrix m)
    (I J : Matrix (Fin m) (Fin r) (ZMod 2)) (hIJ : I.transpose * binaryMatrix P * J = 1)
    (ζ η : Cube (r*k)) :
    character P (freePairingPattern (rankSubstitute I ζ) (rankSubstitute J η)) = character η ζ := by
  rw [character_binary_sum, character_binary_sum]
  apply congrArg binarySign
  have hb (i j) : binaryBit (freePairingPattern (rankSubstitute I ζ) (rankSubstitute J η) (i,j)) =
      ∑ p, J.mulVec (blockCoordinates η p) j * I.mulVec (blockCoordinates ζ p) i := by
    change bitEquiv (bitEquiv.symm _) = _
    rw [Equiv.apply_symm_apply, coordinateDual_apply]
    simp
  calc
    _ = ∑ i, ∑ j, ∑ p, I.mulVec (blockCoordinates ζ p) i *
        (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
      simp only [Fintype.sum_prod_type, hb, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro p hp
      change binaryBit (P (i,j)) * (_ * _) = _ * (binaryBit (P (i,j)) * _)
      ring
    _ = ∑ p, ∑ i, ∑ j, I.mulVec (blockCoordinates ζ p) i *
        (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
      calc
        _ = ∑ i, ∑ p, ∑ j, I.mulVec (blockCoordinates ζ p) i *
            (binaryMatrix P i j * J.mulVec (blockCoordinates η p) j) := by
          apply Finset.sum_congr rfl; intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ p, coordinateDual (I.mulVec (blockCoordinates ζ p))
        ((binaryMatrix P).mulVec (J.mulVec (blockCoordinates η p))) := by
      simp only [coordinateDual_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ = ∑ p, coordinateDual (blockCoordinates ζ p) (blockCoordinates η p) := by
      simp_rw [rank_pairing_contract _ I J hIJ]
    _ = ∑ q, binaryBit (η q) * binaryBit (ζ q) := by
      rw [← Equiv.sum_comp finProdFinEquiv (fun q => binaryBit (η q) * binaryBit (ζ q))]
      simp only [coordinateDual_apply, blockCoordinates, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l hl
      apply Finset.sum_congr rfl; intro p hp
      ring

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem coefficient_rank_walsh_bound (hn : m+m ≤ k+m+m)
    (P : SignMatrix m) (ε δ : Cube m) :
    |fourier (fun S => d.patternPairing hn S ε δ) P| ≤ walshNorm ((binaryMatrix P).rank*k) T := by
  obtain ⟨I,J,hIJ⟩ := exists_rank_pairing_matrix (binaryMatrix P)
  have h := walsh_amplitude_bound d.amplifiedOperator
    (fun ζ => d.coefficientPrimal ε (rankSubstitute I ζ))
    (fun η => d.coefficientDual P δ (rankSubstitute J η))
    (fourier (fun S => d.patternPairing hn S ε δ) P)
    (fun ζ => d.coefficientPrimal_norm ε _) (fun η => d.coefficientDual_norm P δ _)
    (fun ζ η => by rw [d.tagged_coefficient_extraction hn, rankSubstitute_character P I J hIJ, mul_comm])
  exact h.trans_eq (d.walsh_norms _)

end GrowthPairingData

end Cotype

end

end OAI
