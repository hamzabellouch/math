import OAI.MathematicalPhysics.Boltzmann.Branching.CentralRetainedLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedBlockComparison
import Mathlib.Topology.MetricSpace.Sequences

namespace OAI

section

/-! # Bounded endpoint subsequences or escape of their norm -/

noncomputable section

open Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem endpoint_subsequence_or_escape {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (u : ℕ → E) :
    (∃ x : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)) ∨
      Tendsto (fun n => ‖u n‖) atTop atTop := by
  by_cases hb : ∃ R : ℝ, ∃ᶠ n in atTop, ‖u n‖ ≤ R
  · obtain ⟨R,hR⟩ := hb
    have hmem : ∃ᶠ n in atTop, u n ∈ Metric.closedBall (0:E) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hR
    obtain ⟨x,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0:E) R).tendsto_subseq' hmem
    exact Or.inl ⟨x,φ,hφ,hlim⟩
  · right
    apply tendsto_atTop.2
    intro R
    have hnot : ¬ ∃ᶠ n in atTop, ‖u n‖ ≤ R := fun h => hb ⟨R,h⟩
    exact (not_frequently.mp hnot).mono (fun n hn => (lt_of_not_ge hn).le)

end BoltzmannNonuniqueness

end

end

section

/-! # Finite endpoint masses and their passage to a dominated phase measure -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem kernel_lintegral_comp_finset {ι : Type*} (I : Finset ι)
    (K : ι → Kernel X Y) (L : Kernel Y Z) (x : X) {f : Z → ℝ≥0∞} (_hf : Measurable f) :
    (∫⁻ z, f z ∂(L ∘ₖ ∑ i ∈ I, K i) x) =
      ∑ i ∈ I, ∫⁻ z, f z ∂(L ∘ₖ K i) x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi,Kernel.comp_add_right,add_apply,lintegral_add_measure,ih]

theorem endpoint_mass_of_pointwise (K : Kernel (ℝ × WeakTime.Phase) WeakTime.Phase)
    (μ ν : Measure WeakTime.Phase) (s : ℝ) {A B : Set WeakTime.Phase}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (g : ℝ≥0∞)
    (hν : K ∘ₘ WeakTime.phaseSeed s μ ≤ ν)
    (hpoint : ∀ p ∈ B, g ≤ K (s,p) A) :
    g*μ B ≤ ν A := by
  have hh := hν A
  rw [Measure.bind_apply hA K.aemeasurable,WeakTime.phaseSeed,
    lintegral_map (f := fun z => K z A) (K.measurable_coe hA)
      (show Measurable (fun p : WeakTime.Phase => (s,p)) by fun_prop)] at hh
  apply le_trans _ hh
  rw [← lintegral_indicator_const hB]
  apply lintegral_mono
  intro p
  by_cases hp : p ∈ B
  · simpa only [indicator_of_mem hp] using hpoint p hp
  · simp only [indicator_of_notMem hp]
    exact zero_le

end BoltzmannNonuniqueness

end

end

end OAI
