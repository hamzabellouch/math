import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! Strict tail bounds pass to almost-everywhere limits. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LipschitzHilbert

theorem strict_tail_bound_of_ae_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → ℝ) (g : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (t C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, μ.real {x | t < f n x} ≤ C) :
    μ.real {x | t < g x} ≤ C := by
  let S := fun m : ℕ => {x | ∀ n ≥ m, t < f n x}
  have hmono : Monotone S := by
    intro m n hmn x hx i hi
    exact hx i (hmn.trans hi)
  have hsub : ∀ᵐ x ∂μ, x ∈ {x | t < g x} → x ∈ ⋃ m, S m := by
    filter_upwards [hlim] with x hx ht
    have h := (tendsto_order.mp hx).1 t ht
    obtain ⟨m,hm⟩ := eventually_atTop.mp h
    exact mem_iUnion.mpr ⟨m,hm⟩
  have hmass : μ {x | t < g x} ≤ ENNReal.ofReal C := by
    calc
      _ ≤ μ (⋃ m, S m) := measure_mono_ae hsub
      _ = ⨆ m, μ (S m) := hmono.directed_le.measure_iUnion
      _ ≤ ENNReal.ofReal C := by
        apply iSup_le
        intro m
        have hle := ENNReal.ofReal_le_ofReal (hbound m)
        rw [ofReal_measureReal] at hle
        exact (measure_mono (show S m ⊆ {x | t < f m x} from fun _ hx => hx m le_rfl)).trans hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using hreal

end LipschitzHilbert

end

end OAI
