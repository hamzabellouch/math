import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Centering

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {Y : Ω → ℝ} {L : ℝ}

theorem integrable_of_abs_le (hY : AEMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) : Integrable Y μ := by
  apply Integrable.of_mem_Icc (-L) L hY
  filter_upwards [hbound] with ω hω using abs_le.mp hω

omit [IsFiniteMeasure μ] in

theorem abs_sub_condExp_le (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) :
    ∀ᵐ ω ∂μ, |Y ω - μ[Y | m] ω| ≤ 2 * L := by
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hbound
  filter_upwards [hbound, hc] with ω hω hcω
  calc
    |Y ω - μ[Y | m] ω| ≤ |Y ω| + |μ[Y | m] ω| := abs_sub _ _
    _ ≤ L + L := add_le_add hω hcω
    _ = 2 * L := by ring

theorem condExp_sub_condExp_eq_zero (hm : m ≤ mΩ) (hYi : Integrable Y μ) :
    μ[fun ω ↦ Y ω - μ[Y | m] ω | m] =ᵐ[μ] 0 := by
  have hsub := condExp_sub hYi (integrable_condExp (f := Y) (m := m)) m
  have hfix : μ[μ[Y | m] | m] = μ[Y | m] :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp
  simpa only [Pi.sub_def, hfix, sub_self] using hsub

omit [IsFiniteMeasure μ] in

theorem integrable_sub_condExp (hYi : Integrable Y μ) :
    Integrable (fun ω ↦ Y ω - μ[Y | m] ω) μ :=
  hYi.sub integrable_condExp

variable {X : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ}

omit [IsFiniteMeasure μ] in

theorem stronglyMeasurable_centered_increment_of_measurable (j : ℕ)
    (hj : StronglyMeasurable[ℱ j] (X j))
    (hj1 : StronglyMeasurable[ℱ (j + 1)] (X (j + 1))) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by
  exact (hj1.sub (hj.mono (ℱ.mono (Nat.le_succ j)))).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j)))

theorem stronglyMeasurable_increment (hX : StronglyAdapted ℱ X) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω) :=
  (hX (j + 1)).sub ((hX j).mono (ℱ.mono (Nat.le_succ j)))

omit [IsFiniteMeasure μ] in

theorem stronglyMeasurable_centered_increment (hX : StronglyAdapted ℱ X) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by
  exact (stronglyMeasurable_increment hX j).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j)))

theorem sum_centered_increments_eq (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ mΩ)
    (μ : Measure Ω) (t : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range t, (X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)) =
    X t ω - X 0 ω - ∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ X j ω)]

end Balanced

end OAI
