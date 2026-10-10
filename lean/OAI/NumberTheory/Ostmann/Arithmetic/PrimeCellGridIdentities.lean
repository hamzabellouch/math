import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellAssignedSmooth

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open scoped BigOperators
open MeasureTheory PrimeProgression PrimeCellReplacement PrimeCellFreezing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]

omit [Fintype ι] [DecidableEq ι] in
theorem box_order [Fintype ι] [DecidableEq ι] (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) : ∀ i, boxLower lo hi η j i ≤ boxUpper lo hi η j i :=
  fun i => gridPoint_mono (h i) (Nat.le_succ _)

omit [Fintype ι] [DecidableEq ι] in
theorem boxLower_ge [Fintype ι] [DecidableEq ι] (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) : ∀ i, lo i ≤ boxLower lo hi η j i :=
  fun i => (gridPoint_mem (h i) (j i).isLt.le).1

omit [Fintype ι] [DecidableEq ι] in
theorem boxUpper_le [Fintype ι] [DecidableEq ι] (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) : ∀ i, boxUpper lo hi η j i ≤ hi i :=
  fun i => (gridPoint_mem (h i) (show (j i).val+1 ≤ gridCount (lo i) (hi i) (η i) by omega)).2

theorem closedBox_subset (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) :
    logRectangle (boxLower lo hi η j) (boxUpper lo hi η j) ⊆ logRectangle lo hi := by
  intro z hz i hi'
  exact ⟨(boxLower_ge lo hi η h j i).trans (hz i hi').1,
    (hz i hi').2.trans (boxUpper_le lo hi η h j i)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem box_width_le [Fintype ι] [DecidableEq ι] (lo hi η : ι → ℝ)
    (h : ∀ i, lo i ≤ hi i) (hη : ∀ i, 0 < η i)
    (j : GridBoxIndex lo hi η) :
    ∀ i, boxUpper lo hi η j i-boxLower lo hi η j i ≤ η i := by
  intro i
  exact (gridPoint_width _ _ _ _).trans_le (gridStep_le (h i) (hη i))

theorem smoothJointTestSum_eq_sum_assigned (N : ι → ℕ) (lo hi η Z : ι → ℝ)
    (h : ∀ i, lo i ≤ hi i) (F : (ι → (ZMod M)ˣ) → ℂ) (f : (ι → ℝ) → ℂ) :
    smoothJointTestSum N M lo hi Z F f =
      ∑ j : GridBoxIndex lo hi η, smoothAssignedJointTestSum N M lo hi η Z j F f := by
  simpa only [smoothJointTestSum,smoothAssignedJointTestSum,tupleWeight,
    assignedTupleWeight,Complex.ofReal_prod,mul_assoc] using
    sum_product_prime_prior_eq_sum_assigned N lo hi η Z h
      (fun p => jointUnitTest F (fun i => (p i:ZMod M))*f (fun i => (p i:ℝ)))

theorem principalMass_eq_sum_boxes (M : ℕ) (lo hi η Z : ι → ℝ)
    (h : ∀ i, lo i ≤ hi i) (hlo : ∀ i, 0 < lo i) :
    principalMass M lo hi Z = ∑ j : GridBoxIndex lo hi η,
      principalMass M (boxLower lo hi η j) (boxUpper lo hi η j) Z := by
  unfold principalMass
  rw [← residue_logCellMass_eq_prod M Z lo hi h]
  rw [logCellMass_eq_sum_boxes _ lo hi η h hlo]
  apply Finset.sum_congr rfl
  intro j _
  exact residue_logCellMass_eq_prod M Z _ _ (box_order lo hi η h j)

theorem principalIntegral_eq_sum_boxes (M : ℕ) (lo hi η Z : ι → ℝ)
    (h : ∀ i, lo i ≤ hi i) (hlo : ∀ i, 0 < lo i) (f : (ι → ℝ) → ℂ)
    (hf : ContinuousOn (fun t => f (fun i => Real.exp (t i))) (logRectangle lo hi)) :
    principalIntegral M lo hi Z f = ∑ j : GridBoxIndex lo hi η,
      principalIntegral M (boxLower lo hi η j) (boxUpper lo hi η j) Z f := by
  apply integral_rectangle_eq_sum_boxes lo hi η h
  exact ((continuousOn_logCellDensity _ lo hi hlo).smul hf).integrableOn_compact
    (isCompact_logRectangle lo hi)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
