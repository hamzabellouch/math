import OAI.Geometry.RCD.Metric.ProbabilityClosedMass

namespace OAI

/-! # Removing an arbitrarily small enlargement of a closed target ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem finite_measure_closedBall_of_enlargements {n : ℕ}
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ]
    (z : Euclidean n) (R c : ℝ)
    (h : ∀ κ : ℝ, 0 < κ → c ≤ μ.real (closedBall z (R+κ))) :
    c ≤ μ.real (closedBall z R) := by
  let A := fun j : ℕ => closedBall z (R+1/((j:ℝ)+1))
  have hanti : Antitone A := by
    intro i j hij
    apply closedBall_subset_closedBall
    apply add_le_add le_rfl
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hrad : Tendsto (fun j : ℕ => R+1/((j:ℝ)+1)) atTop (𝓝 R) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add R
  have he : (⋂ j, A j)=closedBall z R := by
    ext x
    simp only [mem_iInter,mem_closedBall,A]
    constructor
    · intro hx
      exact ge_of_tendsto hrad (Eventually.of_forall hx)
    · intro hx j
      exact hx.trans (le_add_of_nonneg_right (by positivity))
  have hA (j : ℕ) : MeasurableSet (A j) := measurableSet_closedBall
  have hm := tendsto_measure_iInter_atTop (μ := μ)
    (fun j => (hA j).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
  rw [he] at hm
  have hr := (ENNReal.tendsto_toReal (measure_ne_top μ (closedBall z R))).comp hm
  change Tendsto (fun j => μ.real (A j)) atTop (𝓝 (μ.real (closedBall z R))) at hr
  exact ge_of_tendsto hr (Eventually.of_forall fun j => h _ (by positivity))

end RegularPointCoordinates

end

end OAI
