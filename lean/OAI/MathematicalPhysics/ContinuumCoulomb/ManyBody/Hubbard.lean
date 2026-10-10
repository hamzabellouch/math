import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.Spin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

namespace OAI

/-!
# Two-site Hubbard superexchange

The four canonical fermion modes are `L↑, L↓, R↑, R↓`, in that order.
Creation and annihilation use the parity of occupied modes preceding the
acted-on mode.  Thus the hopping signs are computed from the canonical
fermionic action, rather than assumed as transition amplitudes.

Only the two-electron sector used by the Coulomb reductions is needed.
Its first four basis states are singly occupied, followed by the left and
right doubly occupied states.  The penalty of either virtual excitation
is `U - v`, including the intersite direct Coulomb contribution.
-/

noncomputable section

namespace ContinuumCoulomb

open Matrix
open scoped BigOperators

abbrev FourModeOccupation := Finset (Fin 4)
abbrev FourModeFock := FourModeOccupation →₀ ℂ

def fermionParity (p : Fin 4) (s : FourModeOccupation) : ℂ :=
  (-1) ^ (s.filter (fun q => q < p)).card

def createBasis (p : Fin 4) (s : FourModeOccupation) : FourModeFock :=
  if p ∈ s then 0 else fermionParity p s • Finsupp.single (insert p s) 1

def annihilateBasis (p : Fin 4) (s : FourModeOccupation) : FourModeFock :=
  if p ∈ s then fermionParity p s • Finsupp.single (s.erase p) 1 else 0

def fermionCreate (p : Fin 4) : FourModeFock →ₗ[ℂ] FourModeFock :=
  Finsupp.linearCombination ℂ (createBasis p)

def fermionAnnihilate (p : Fin 4) : FourModeFock →ₗ[ℂ] FourModeFock :=
  Finsupp.linearCombination ℂ (annihilateBasis p)

theorem fermionCreate_single (p : Fin 4) (s : FourModeOccupation) (z : ℂ) :
    fermionCreate p (Finsupp.single s z) = z • createBasis p s :=
  Finsupp.linearCombination_single ℂ z s

theorem fermionAnnihilate_single (p : Fin 4) (s : FourModeOccupation) (z : ℂ) :
    fermionAnnihilate p (Finsupp.single s z) = z • annihilateBasis p s :=
  Finsupp.linearCombination_single ℂ z s

def twoElectronOccupation (i : Fin 6) : FourModeOccupation :=
  ![{0, 2}, {0, 3}, {1, 2}, {1, 3}, {0, 1}, {2, 3}] i

def twoElectronBasis (i : Fin 6) : FourModeFock :=
  Finsupp.single (twoElectronOccupation i) 1

/-- Unit hopping amplitude, with the conventional minus sign. -/
def twoSiteHopping : FourModeFock →ₗ[ℂ] FourModeFock :=
  -((fermionCreate 0).comp (fermionAnnihilate 2) +
    (fermionCreate 2).comp (fermionAnnihilate 0) +
    (fermionCreate 1).comp (fermionAnnihilate 3) +
    (fermionCreate 3).comp (fermionAnnihilate 1))

theorem twoSiteHopping_up_up : twoSiteHopping (twoElectronBasis 0) = 0 := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.filter_insert, Finset.filter_singleton, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]

theorem twoSiteHopping_up_down :
    twoSiteHopping (twoElectronBasis 1) = -(twoElectronBasis 4 + twoElectronBasis 5) := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.insert_comm, Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]
  abel

theorem twoSiteHopping_down_up :
    twoSiteHopping (twoElectronBasis 2) = twoElectronBasis 4 + twoElectronBasis 5 := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.insert_comm, Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]
  abel

theorem twoSiteHopping_down_down : twoSiteHopping (twoElectronBasis 3) = 0 := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.filter_insert, Finset.filter_singleton, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]

theorem twoSiteHopping_double_left :
    twoSiteHopping (twoElectronBasis 4) = -twoElectronBasis 1 + twoElectronBasis 2 := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.insert_comm, Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]

theorem twoSiteHopping_double_right :
    twoSiteHopping (twoElectronBasis 5) = -twoElectronBasis 1 + twoElectronBasis 2 := by
  norm_num [twoSiteHopping, twoElectronBasis, twoElectronOccupation,
    fermionCreate_single, fermionAnnihilate_single, createBasis, annihilateBasis,
    fermionParity, Finset.insert_comm, Finset.filter_insert, Finset.filter_singleton,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.pair_comm]
  module

/-- Matrix of the actual canonical hopping action on the two-electron sector. -/
def twoSiteHoppingMatrix : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, -1, -1;
     0, 0, 0, 0, 1, 1;
     0, 0, 0, 0, 0, 0;
     0, -1, 1, 0, 0, 0;
     0, -1, 1, 0, 0, 0]

theorem twoSiteHopping_basis (i : Fin 6) :
    twoSiteHopping (twoElectronBasis i) =
      ∑ j, twoSiteHoppingMatrix j i • twoElectronBasis j := by
  fin_cases i <;>
    simp [twoSiteHoppingMatrix, Fin.sum_univ_succ, twoSiteHopping_up_up,
      twoSiteHopping_up_down, twoSiteHopping_down_up, twoSiteHopping_down_down,
      twoSiteHopping_double_left, twoSiteHopping_double_right, neg_add_rev]
  all_goals abel

/-- Occupancy deviation at the left site. -/
def leftOccupancyDeviation (s : FourModeOccupation) : ℝ :=
  ((s.filter (fun p => p < 2)).card : ℝ) - 1

def rightOccupancyDeviation (s : FourModeOccupation) : ℝ :=
  ((s.filter (fun p => 2 ≤ p)).card : ℝ) - 1

/-- The quadratic Coulomb occupancy penalty before the scalar `-v` shift. -/
def twoSiteOccupancyPenalty (U v : ℝ) (s : FourModeOccupation) : ℝ :=
  U / 2 * (leftOccupancyDeviation s ^ 2 + rightOccupancyDeviation s ^ 2) +
    v * leftOccupancyDeviation s * rightOccupancyDeviation s

theorem twoSiteOccupancyPenalty_basis (U v : ℝ) (i : Fin 6) :
    twoSiteOccupancyPenalty U v (twoElectronOccupation i) =
      if i < 4 then 0 else U - v := by
  fin_cases i <;>
    norm_num [twoSiteOccupancyPenalty, leftOccupancyDeviation, rightOccupancyDeviation,
      twoElectronOccupation, Finset.filter_insert, Finset.filter_singleton] <;> ring

/-- The hopping block from the singly occupied spin space to virtual pairs. -/
def twoSiteHoppingBlock : Matrix (Fin 4) (Fin 2) ℂ :=
  !![0, 0; -1, -1; 1, 1; 0, 0]

theorem twoSiteHoppingMatrix_low_block (i j : Fin 4) :
    twoSiteHoppingMatrix (Fin.castAdd 2 i) (Fin.castAdd 2 j) = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [twoSiteHoppingMatrix]

theorem twoSiteHoppingMatrix_cross_block (i : Fin 4) (j : Fin 2) :
    twoSiteHoppingMatrix (Fin.castAdd 2 i) (Fin.natAdd 4 j) =
      twoSiteHoppingBlock i j := by
  fin_cases i <;> fin_cases j <;> norm_num [twoSiteHoppingMatrix, twoSiteHoppingBlock]

theorem twoSiteHoppingBlock_square :
    twoSiteHoppingBlock * twoSiteHoppingBlock.transpose =
      (1 : Matrix (Fin 4) (Fin 4) ℂ) - heisenberg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteHoppingBlock, heisenberg, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- Exact negative second-order compression with excitation cost `U-v`. -/
def twoSiteSecondOrder (t U v : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-(t ^ 2 / (U - v) : ℝ) : ℂ) •
    (twoSiteHoppingBlock * twoSiteHoppingBlock.transpose)

theorem twoSiteSecondOrder_eq (t U v : ℝ) :
    twoSiteSecondOrder t U v =
      ((t ^ 2 / (U - v) : ℝ) : ℂ) • (heisenberg - 1) := by
  rw [twoSiteSecondOrder, twoSiteHoppingBlock_square]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The manuscript's hopping calibration gives the required exchange,
while the intersite interaction remains in its virtual denominator. -/
theorem twoSiteSecondOrder_calibrated
    {t U v τ K : ℝ} (hgap : U - v ≠ 0)
    (ht : t ^ 2 = τ ^ 2 * K * (U - v)) :
    twoSiteSecondOrder t U v =
      ((τ ^ 2 * K : ℝ) : ℂ) • (heisenberg - 1) := by
  rw [twoSiteSecondOrder_eq, ht, mul_div_cancel_right₀ _ hgap]

/-- The inverse penalty vanishes on the singly occupied kernel. -/
def twoSiteInversePenaltyMatrix (U v : ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal fun i => if i < 4 then 0 else ((U - v : ℝ) : ℂ)⁻¹

/-- Compression of the actual six-dimensional negative inverse term. -/
def twoSiteCompressedInverseTerm (t U v : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => -((t ^ 2 : ℝ) : ℂ) *
    (twoSiteHoppingMatrix * twoSiteInversePenaltyMatrix U v * twoSiteHoppingMatrix)
      (Fin.castAdd 2 i) (Fin.castAdd 2 j)

theorem twoSiteCompressedInverseTerm_eq (t U v : ℝ) :
    twoSiteCompressedInverseTerm t U v = twoSiteSecondOrder t U v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteCompressedInverseTerm, twoSiteInversePenaltyMatrix,
      Matrix.mul_apply, Matrix.mul_diagonal, twoSiteHoppingMatrix,
      twoSiteSecondOrder, twoSiteHoppingBlock, Fin.sum_univ_succ,
      Complex.ofReal_div, div_eq_mul_inv, Matrix.vecMul, Matrix.transpose_apply,
      dotProduct, Matrix.diagonal_apply]
  all_goals ring

end ContinuumCoulomb

end

end OAI
