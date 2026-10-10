import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionBoxes
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellIntegralFreezingMass

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open MeasureTheory PrimeCellFreezing MixedCellIntegralFreezing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MixedGridIndex (loI hiI ηI : ℝ) (lo hi η : ι → ℝ) :=
  Fin (gridCount loI hiI ηI) × GridBoxIndex lo hi η

def assignedMixedBox (loI hiI ηI : ℝ) (lo hi η : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) : Set (ℝ × (ι → ℝ)) :=
  assignedCell loI hiI ηI j.1 ×ˢ assignedBox lo hi η j.2

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMixedBox_subset {loI hiI ηI : ℝ} {lo hi η : ι → ℝ}
    (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i) (j : MixedGridIndex loI hiI ηI lo hi η) :
    assignedMixedBox loI hiI ηI lo hi η j ⊆ mixedLogRectangle loI hiI lo hi := by
  intro t ht
  exact ⟨assignedCell_subset_interval hI j.1 ht.1,assignedBox_subset_rectangle h j.2 ht.2⟩

omit [Fintype ι] [DecidableEq ι] in
theorem iUnion_assignedMixedBox {loI hiI ηI : ℝ} {lo hi η : ι → ℝ}
    (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i) :
    (⋃ j : MixedGridIndex loI hiI ηI lo hi η, assignedMixedBox loI hiI ηI lo hi η j) =
      mixedLogRectangle loI hiI lo hi := by
  ext t
  constructor
  · rintro ht
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ht
    exact assignedMixedBox_subset hI h j hj
  · intro ht
    obtain ⟨j,hj⟩ := exists_assignedCell (η:=ηI) hI ht.1
    have hp : t.2 ∈ ⋃ k : GridBoxIndex lo hi η, assignedBox lo hi η k := by
      rw [iUnion_assignedBox h]
      exact ht.2
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨(j,k),hj,hk⟩

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMixedBox_pairwiseDisjoint {loI hiI ηI : ℝ} {lo hi η : ι → ℝ}
    (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i) :
    Pairwise (fun j k : MixedGridIndex loI hiI ηI lo hi η =>
      Disjoint (assignedMixedBox loI hiI ηI lo hi η j) (assignedMixedBox loI hiI ηI lo hi η k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro t htj htk
  by_cases hfirst : j.1=k.1
  · have hsecond : j.2≠k.2 := fun hh => hjk (Prod.ext hfirst hh)
    exact Set.disjoint_left.mp (assignedBox_pairwiseDisjoint h hsecond) htj.2 htk.2
  · exact Set.disjoint_left.mp (assignedCell_pairwiseDisjoint hI hfirst) htj.1 htk.1

omit [DecidableEq ι] in
theorem assignedMixedBox_ae_eq_closed (loI hiI ηI : ℝ) (lo hi η : ι → ℝ)
    (j : MixedGridIndex loI hiI ηI lo hi η) :
    assignedMixedBox loI hiI ηI lo hi η j =ᵐ[volume]
      mixedLogRectangle (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
        (boxLower lo hi η j.2) (boxUpper lo hi η j.2) := by
  exact Measure.set_prod_ae_eq (assignedCell_ae_eq_closed loI hiI ηI j.1)
    (assignedBox_ae_eq_closed lo hi η j.2)

theorem integral_mixedRectangle_eq_sum_boxes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (loI hiI ηI : ℝ) (lo hi η : ι → ℝ) (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i)
    (f : (ℝ × (ι → ℝ)) → E) (hf : IntegrableOn f (mixedLogRectangle loI hiI lo hi)) :
    (∫ t in mixedLogRectangle loI hiI lo hi, f t) =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        ∫ t in mixedLogRectangle (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1))
          (boxLower lo hi η j.2) (boxUpper lo hi η j.2), f t := by
  have hm (j : MixedGridIndex loI hiI ηI lo hi η) :
      MeasurableSet (assignedMixedBox loI hiI ηI lo hi η j) :=
    (measurableSet_assignedCell loI hiI ηI j.1).prod (measurableSet_assignedBox lo hi η j.2)
  have hint (j : MixedGridIndex loI hiI ηI lo hi η) :
      IntegrableOn f (assignedMixedBox loI hiI ηI lo hi η j) :=
    hf.mono_set (assignedMixedBox_subset hI h j)
  rw [← iUnion_assignedMixedBox (ηI:=ηI) (η:=η) hI h]
  rw [integral_iUnion_fintype hm (assignedMixedBox_pairwiseDisjoint hI h) hint]
  apply Finset.sum_congr rfl
  intro j hj
  exact setIntegral_congr_set (assignedMixedBox_ae_eq_closed loI hiI ηI lo hi η j)

theorem mixedLogMass_eq_sum_boxes (M : ℕ) (loI hiI ηI G : ℝ) (φ : ℝ → ℝ)
    (w lo hi η : ι → ℝ) (hI : loI ≤ hiI) (h : ∀ i, lo i ≤ hi i)
    (hφ : Continuous φ) (hlo : ∀ i, 0 < lo i) :
    mixedLogMass M loI hiI G φ w lo hi =
      ∑ j : MixedGridIndex loI hiI ηI lo hi η,
        mixedLogMass M (gridPoint loI hiI ηI j.1.val) (gridPoint loI hiI ηI (j.1.val+1)) G φ w
          (boxLower lo hi η j.2) (boxUpper lo hi η j.2) :=
  integral_mixedRectangle_eq_sum_boxes loI hiI ηI lo hi η hI h _
    (integrableOn_mixedLogDensity M loI hiI G φ w lo hi hφ hlo)

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
