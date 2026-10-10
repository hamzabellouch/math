import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionGrid
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellIntegralFreezing

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open MeasureTheory PrimeCellFreezing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev GridBoxIndex (lo hi η : ι → ℝ) := ∀ i, Fin (gridCount (lo i) (hi i) (η i))

def boxLower (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) (i : ι) : ℝ :=
  gridPoint (lo i) (hi i) (η i) (j i).val

def boxUpper (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) (i : ι) : ℝ :=
  gridPoint (lo i) (hi i) (η i) ((j i).val+1)

def assignedBox (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) : Set (ι → ℝ) :=
  Set.univ.pi fun i => assignedCell (lo i) (hi i) (η i) (j i)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedBox_subset_rectangle {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i)
    (j : GridBoxIndex lo hi η) : assignedBox lo hi η j ⊆ logRectangle lo hi := by
  intro t ht i hi'
  exact assignedCell_subset_interval (h i) (j i) (ht i hi')

omit [Fintype ι] [DecidableEq ι] in
theorem iUnion_assignedBox {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i) :
    (⋃ j : GridBoxIndex lo hi η, assignedBox lo hi η j) = logRectangle lo hi := by
  ext t
  constructor
  · intro ht
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ht
    exact assignedBox_subset_rectangle h j hj
  · intro ht
    have hc : ∀ i, ∃ j : Fin (gridCount (lo i) (hi i) (η i)),
        t i ∈ assignedCell (lo i) (hi i) (η i) j :=
      fun i => exists_assignedCell (h i) (ht i (Set.mem_univ i))
    choose j hj using hc
    exact Set.mem_iUnion.mpr ⟨j,fun i _ => hj i⟩

omit [Fintype ι] [DecidableEq ι] in
theorem assignedBox_pairwiseDisjoint {lo hi η : ι → ℝ} (h : ∀ i, lo i ≤ hi i) :
    Pairwise (fun j k : GridBoxIndex lo hi η => Disjoint (assignedBox lo hi η j) (assignedBox lo hi η k)) := by
  intro j k hjk
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  exact Set.disjoint_left.mp (assignedCell_pairwiseDisjoint (h i) hi)
    (htj i (Set.mem_univ i)) (htk i (Set.mem_univ i))

omit [DecidableEq ι] in
theorem measurableSet_assignedBox (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) :
    MeasurableSet (assignedBox lo hi η j) :=
  MeasurableSet.univ_pi fun i => measurableSet_assignedCell (lo i) (hi i) (η i) (j i)

omit [DecidableEq ι] in
theorem assignedBox_ae_eq_closed (lo hi η : ι → ℝ) (j : GridBoxIndex lo hi η) :
    assignedBox lo hi η j =ᵐ[volume] logRectangle (boxLower lo hi η j) (boxUpper lo hi η j) := by
  change (Set.univ.pi fun i => assignedCell (lo i) (hi i) (η i) (j i)) =ᵐ[Measure.pi (fun _ : ι => (volume : Measure ℝ))]
    (Set.univ.pi fun i => Set.Icc (boxLower lo hi η j i) (boxUpper lo hi η j i))
  exact Measure.ae_eq_set_pi fun i _ => assignedCell_ae_eq_closed (lo i) (hi i) (η i) (j i)

theorem integral_rectangle_eq_sum_boxes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lo hi η : ι → ℝ) (h : ∀ i, lo i ≤ hi i) (f : (ι → ℝ) → E)
    (hf : IntegrableOn f (logRectangle lo hi)) :
    (∫ t in logRectangle lo hi, f t) =
      ∑ j : GridBoxIndex lo hi η, ∫ t in logRectangle (boxLower lo hi η j) (boxUpper lo hi η j), f t := by
  rw [← iUnion_assignedBox (η:=η) h]
  rw [integral_iUnion_fintype (measurableSet_assignedBox lo hi η)
    (assignedBox_pairwiseDisjoint h) (fun j => hf.mono_set (assignedBox_subset_rectangle h j))]
  apply Finset.sum_congr rfl
  intro j hj
  exact setIntegral_congr_set (assignedBox_ae_eq_closed lo hi η j)

theorem logCellMass_eq_sum_boxes (w lo hi η : ι → ℝ)
    (h : ∀ i, lo i ≤ hi i) (hlo : ∀ i, 0 < lo i) :
    logCellMass w lo hi = ∑ j : GridBoxIndex lo hi η,
      logCellMass w (boxLower lo hi η j) (boxUpper lo hi η j) :=
  integral_rectangle_eq_sum_boxes lo hi η h (logCellDensity w)
    (integrableOn_logCellDensity w lo hi hlo)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
