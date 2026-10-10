import Mathlib
import OAI.Analysis.LaughlinFock.PairDecomposition

namespace OAI

/-! Copy Vectors. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem pairAnnihilator_increasing (Q p : ℕ) :
    pairAnnihilator Q p = ∑ ij : IncreasingPair Q,
      (pairCoefficient Q p ij.val.1 ij.val.2 : ℂ) •
        (annihilator Q ij.val.2 * annihilator Q ij.val.1) := by
  rw [increasingPair_sum Q (fun i j =>
    (pairCoefficient Q p i j : ℂ) • (annihilator Q j * annihilator Q i))]
  rfl

 

theorem wedgeCoupledCoefficient_one_eq_pair {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (ij : IncreasingPair Q) :
    wedgeCoupledCoefficient Q 1 p ij = pairCoefficient Q p ij.val.1 ij.val.2 := by
  rw [pairCoefficient_eq_coupled hQ hp]
  rfl

 

def wideFourWedgeMatrix (Q : ℕ) :
    Matrix (SectorOccupation Q 4) (FourUncoupled Q) ℂ := fun A b =>
  annihilatorVector Q 4
    (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val) A

theorem wideFourAnnihilator_mem (Q : ℕ) (b : FourUncoupled Q) :
    annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val ∈
      AnnihilationSpace Q 4 :=
  annihilationSpace_mul Q 2 2 (pairAnnihilator_mem Q b.1.val)
    (annihilationSpace_mul Q 1 1 (annihilator_mem Q b.2.val.1) (annihilator_mem Q b.2.val.2))

theorem wideFourWedgeMatrix_annihilator_column (Q : ℕ) (b : FourUncoupled Q) :
    wedgeAnnihilator Q 4 (fun A => wideFourWedgeMatrix Q A b) =
      annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val :=
  wedgeAnnihilator_annihilatorVector Q 4 _ (wideFourAnnihilator_mem Q b)

 

def composedFourWedgeColumn (Q r z k : ℕ) : SectorOccupation Q 4 → ℂ :=
  wideFourWedgeMatrix Q *ᵥ fun b => (composedCoupledVector Q r z k b : ℂ)

 
def composedFourAnnihilator (Q r z k : ℕ) : FockMatrix Q :=
  ∑ b : FourUncoupled Q, (composedCoupledVector Q r z k b : ℂ) •
    (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val)

theorem composedFourAnnihilator_eq_wedge (Q r z k : ℕ) :
    composedFourAnnihilator Q r z k = wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r z k) := by
  unfold composedFourWedgeColumn
  rw [wedgeAnnihilator_mulVec]
  simp only [wideFourWedgeMatrix_annihilator_column, Complex.star_def,
    Complex.conj_ofReal, composedFourAnnihilator]

 

theorem highestFourAnnihilator_eq_composed {Q D : ℕ} (hD : D ≤ Q) (r : CopyLabel D) :
    highestFourAnnihilator Q D r = composedFourAnnihilator Q r.val.val (D-r.val.val) 0 := by
  classical
  have hr : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
  have h := sum_subtype_support
    (fun b : FourUncoupled Q => b.1.val+b.2.val.1.val+b.2.val.2.val=D)
    (fun b : FourUncoupled Q =>
      (sphericalCopyCoefficient Q D D r.val.val b.1.val b.2.val.1.val b.2.val.2.val : ℂ) •
        (annihilator Q b.2.val.2 * annihilator Q b.2.val.1 * pairAnnihilator Q b.1.val))
    (by intro b hb; simp [sphericalCopyCoefficient, hb])
  change (∑ b : FourHighestShell Q D,
    (sphericalCopyCoefficient Q D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val : ℂ) •
      (annihilator Q b.val.2.val.2 * annihilator Q b.val.2.val.1 * pairAnnihilator Q b.val.1.val)) = _
  rw [h]
  unfold composedFourAnnihilator
  apply Finset.sum_congr rfl
  intro b _
  rw [← composedCoupledVector_eq_sphericalCopy hr (le_refl D) hD r.property b]
  simp only [Nat.sub_self]

 
theorem highestFourAnnihilator_eq_wedge {Q D : ℕ} (hD : D ≤ Q) (r : CopyLabel D) :
    highestFourAnnihilator Q D r =
      wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r.val.val (D-r.val.val) 0) := by
  rw [highestFourAnnihilator_eq_composed hD, composedFourAnnihilator_eq_wedge]

 

theorem composedFourAnnihilator_one {Q : ℕ} (hQ : 1 ≤ Q) (z k : ℕ) :
    composedFourAnnihilator Q 1 z k = fourCoupledAnnihilator Q z k := by
  classical
  calc
    _ = ∑ p : Fin (2*Q-2+1), ∑ a : Fin (2*Q-2+1),
        (coupledVector (2*Q-2) (2*Q-2) z k p.val a.val : ℂ) •
          (pairAnnihilator Q a.val * pairAnnihilator Q p.val) := by
      simp only [composedFourAnnihilator, Fintype.sum_prod_type, composedCoupledVector,
        Nat.mul_one, Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [pairAnnihilator_increasing Q a.val, Matrix.sum_mul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro ij _
      rw [wedgeCoupledCoefficient_one_eq_pair hQ (Nat.le_of_lt_succ a.isLt)]
      simp only [Matrix.smul_mul, smul_smul]
    _ = _ := by
      rw [show 2*Q-2+1 = 2*Q-1 by omega]
      rfl

 
theorem annihilatorVector_wedgeAnnihilator (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    annihilatorVector Q k (wedgeAnnihilator Q k v) = v := by
  classical
  funext A
  simp only [annihilatorVector, wedgeAnnihilator, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, basisAnnihilator_vacuum, Subtype.val_inj, mul_ite, mul_one, mul_zero]
  simp

 
theorem wedgeAnnihilator_injective (Q k : ℕ) : Function.Injective (wedgeAnnihilator Q k) := by
  intro v w h
  have hv := congrArg (annihilatorVector Q k) h
  simpa only [annihilatorVector_wedgeAnnihilator] using hv

 

theorem composedFourWedgeColumn_one {Q : ℕ} (hQ : 1 ≤ Q)
    (c : CoupledIndex (2*Q-2) (2*Q-2)) :
    composedFourWedgeColumn Q 1 c.1.val c.2.val =
      fun A => fourCoupledWedgeMatrix Q A c := by
  apply wedgeAnnihilator_injective Q 4
  rw [← composedFourAnnihilator_eq_wedge, composedFourAnnihilator_one hQ,
    fourCoupledAnnihilator_eq_wedge]

 
theorem fourCoupledWedgeMatrix_even_deficit_zero (Q : ℕ)
    (c : CoupledIndex (2*Q-2) (2*Q-2)) (ho : Odd c.1.val) :
    (fun A => fourCoupledWedgeMatrix Q A c) = 0 := by
  apply wedgeAnnihilator_injective Q 4
  rw [← fourCoupledAnnihilator_eq_wedge,
    fourCoupledAnnihilator_odd_zero (coupledIndex_bounds c).1 ho]
  simp [wedgeAnnihilator]

end LaughlinFock
end

end OAI
