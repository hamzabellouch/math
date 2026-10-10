import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Invariant233.Fields

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ae_mem_of_closed_approximation
    {βn : ℕ → FiniteMeasure X} {β : FiniteMeasure X}
    (hβ : Tendsto βn atTop (𝓝 β)) {Z : Set X} (hZ : MeasurableSet Z)
    (happrox : ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X,
      IsClosed K ∧ K ⊆ Z ∧ ∀ n,
        (βn n : Measure X) univ ≤ (βn n : Measure X) K + (ε : ℝ≥0∞)) :
    ∀ᵐ x ∂(β : Measure X), x ∈ Z := by
  have hmass : Tendsto (fun n => (βn n : Measure X) univ) atTop
      (𝓝 ((β : Measure X) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      (ENNReal.continuous_coe.tendsto β.mass).comp hβ.mass
  have hle : (β : Measure X) univ ≤ (β : Measure X) Z := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨K, hKclosed, hKZ, hKn⟩ := happrox ε hε
    calc
      (β : Measure X) univ = limsup (fun n => (βn n : Measure X) univ) atTop :=
        hmass.limsup_eq.symm
      _ ≤ limsup (fun n => (βn n : Measure X) K + (ε : ℝ≥0∞)) atTop :=
        limsup_le_limsup (Eventually.of_forall hKn)
      _ = limsup (fun n => (βn n : Measure X) K) atTop + (ε : ℝ≥0∞) :=
        limsup_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
      _ ≤ (β : Measure X) K + (ε : ℝ≥0∞) :=
        add_le_add (FiniteMeasure.limsup_measure_closed_le_of_tendsto hβ hKclosed) le_rfl
      _ ≤ (β : Measure X) Z + (ε : ℝ≥0∞) :=
        add_le_add (measure_mono hKZ) le_rfl
  have heq : (β : Measure X) Z = (β : Measure X) univ :=
    le_antisymm (measure_mono (subset_univ _)) hle
  rw [ae_iff]
  change (β : Measure X) Zᶜ = 0
  rw [measure_compl hZ (measure_ne_top _ _), heq, tsub_self]

end Invariant233.Fields

end OAI
