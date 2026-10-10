import OAI.Analysis.FiniteFactor.CrossedProduct.FreeRotation
import OAI.Analysis.FiniteFactor.CrossedProduct.TorusModel

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceSmallPartitionSet (n : ℕ) (j : Fin n) : Set (SourceCoordinate → ℝ) :=
  {x | x sourceFirstCoordinate ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))}

theorem sourceSmallPartitionSet_measurable (n : ℕ) (j : Fin n) :
    MeasurableSet (sourceSmallPartitionSet n j) :=
  measurableSet_Ico.preimage (measurable_pi_apply sourceFirstCoordinate)

theorem unitInterval_partition_unique (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : t ∈ Set.Ico 0 1) :
    ∃! j : Fin n, t ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 ≤ (n : ℝ)*t := mul_nonneg hnR.le ht.1
  have hlt : Nat.floor ((n : ℝ)*t) < n :=
    (Nat.floor_lt hnt).mpr (by nlinarith [ht.2])
  let k : Fin n := ⟨Nat.floor ((n : ℝ)*t),hlt⟩
  have he (j : Fin n) : t ∈ Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ)) ↔
      Nat.floor ((n : ℝ)*t) = j.val := by
    rw [Nat.floor_eq_iff hnt]
    change _ ≤ t ∧ t < _ ↔ _ ≤ _ ∧ _ < _
    rw [div_le_iff₀ hnR,lt_div_iff₀ hnR]
    simp only [mul_comm]
  refine ⟨k,(he k).mpr rfl,?_⟩
  intro j hj
  exact Fin.ext ((he j).mp hj).symm

theorem sourceSmallPartition_indicator_sum (n : ℕ) (hn : 0 < n)
    (x : SourceCoordinate → ℝ) (hx : x sourceFirstCoordinate ∈ Set.Ico 0 1) :
    ∑ j : Fin n, (sourceSmallPartitionSet n j).indicator (fun _ => (1 : ℂ)) x = 1 := by
  classical
  obtain ⟨k,hk,hunique⟩ := unitInterval_partition_unique n hn (x sourceFirstCoordinate) hx
  have hk' : x ∈ sourceSmallPartitionSet n k := hk
  rw [Finset.sum_eq_single k]
  · exact Set.indicator_of_mem hk' _
  · intro j _ hj
    exact Set.indicator_of_notMem (s := sourceSmallPartitionSet n j) (a := x)
      (fun h => hj (hunique j h)) (fun _ => (1 : ℂ))
  · simp

/-- Every cell has mass at most 1/n under the actual product Haar measure. -/
theorem sourceSmallPartitionSet_measure_le (n : ℕ) (_hn : 0 < n) (j : Fin n) :
    sourceSamplingHaar (sourceSmallPartitionSet n j) ≤ ENNReal.ofReal (1/(n : ℝ)) := by
  change sourceSamplingHaar ((fun x => x sourceFirstCoordinate) ⁻¹'
    Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))) ≤ _
  rw [← Measure.map_apply (measurable_pi_apply sourceFirstCoordinate) measurableSet_Ico,
    Measure.infinitePi_map_eval]
  calc
    unitIntervalMeasure _ ≤ volume (Set.Ico ((j : ℝ)/(n : ℝ)) (((j : ℝ)+1)/(n : ℝ))) :=
      Measure.restrict_apply_le _ _
    _ = _ := by
      rw [Real.volume_Ico]
      congr 1
      ring

end
end FiniteFactor

end OAI
