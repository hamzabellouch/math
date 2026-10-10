import OAI.Probability.SLE.BrownianStrongMarkov

namespace OAI

/-! The original stopped-past filtration after a finite stopping time.
This keeps the restart comparison on raw sigma algebras. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}

theorem stopping_time_add_nnreal
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω:WithTop ℝ≥0))) (t : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => ((τ ω+t:ℝ≥0):WithTop ℝ≥0)) := by
  intro r
  by_cases htr : t ≤ r
  · have he : {ω | ((τ ω+t:ℝ≥0):WithTop ℝ≥0) ≤ r} =
        {ω | (τ ω:WithTop ℝ≥0) ≤ ((r-t:ℝ≥0):WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe]
      exact (le_tsub_iff_right htr).symm
    rw [he]
    exact ℱ.mono (tsub_le_self : r-t ≤ r) _ (hτ (r-t))
  · have he : {ω | ((τ ω+t:ℝ≥0):WithTop ℝ≥0) ≤ r} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hle : τ ω+t ≤ r := by exact_mod_cast hω
      exact htr ((le_add_left le_rfl).trans hle)
    rw [he]
    exact @MeasurableSet.empty Ω (ℱ r)

def shiftedStoppingFiltration
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω:WithTop ℝ≥0))) : Filtration ℝ≥0 mΩ where
  seq t := (stopping_time_add_nnreal hτ t).measurableSpace
  mono' := by
    intro s t hst
    apply IsStoppingTime.measurableSpace_mono
      (stopping_time_add_nnreal hτ s) (stopping_time_add_nnreal hτ t)
    intro ω
    change ((τ ω+s:ℝ≥0):WithTop ℝ≥0) ≤ ((τ ω+t:ℝ≥0):WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (add_le_add le_rfl hst)
  le' t := (stopping_time_add_nnreal hτ t).measurableSpace_le

theorem shiftedStopping_adapted
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω:WithTop ℝ≥0)))
    (X : ℝ≥0 → Ω → ℝ) (hX : IsStronglyProgressive ℱ X) :
    StronglyAdapted (shiftedStoppingFiltration hτ) (fun t ω => X (τ ω+t) ω) := by
  intro t
  have h := measurable_stoppedValue hX (stopping_time_add_nnreal hτ t)
  change StronglyMeasurable[(stopping_time_add_nnreal hτ t).measurableSpace]
    (fun ω => X (τ ω+t) ω)
  convert h.stronglyMeasurable using 1
  funext ω
  change X (τ ω+t) ω = X (((τ ω+t:ℝ≥0):WithTop ℝ≥0).untopA) ω
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
  rfl

end SLEExactGauge

end

end OAI
