import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Continuity

namespace OAI

/-!
# Limits of decreasing original-pair filters

For the manuscript application, `ρ` is the original product measure with
the bounded distance weight, and `f` is the original distance map. These
lemmas do not replace distances by those of any auxiliary projection.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def filteredPushforward (f : X → Y) (ρ : Measure X) (G : Set X) : Measure Y :=
  Measure.map f (ρ.restrict G)

theorem filteredPushforward_mono (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G H : Set X} (hGH : G ⊆ H) :
    filteredPushforward f ρ G ≤ filteredPushforward f ρ H :=
  Measure.map_mono (Measure.restrict_mono hGH le_rfl) hf

theorem filteredPushforward_mass (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) (G : Set X) : filteredPushforward f ρ G univ = ρ G := by
  rw [filteredPushforward, Measure.map_apply hf MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ]

instance filteredPushforward_finite (f : X → Y) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : Set X) : IsFiniteMeasure (filteredPushforward f ρ G) :=
  inferInstanceAs (IsFiniteMeasure (Measure.map f (ρ.restrict G)))

/-- Decreasing filters produce a decreasing sequence of pushforwards. -/
theorem antitone_filteredPushforward (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G : ℕ → Set X} (hG : Antitone G) :
    Antitone (fun n => filteredPushforward f ρ (G n)) := by
  intro i j hij
  exact filteredPushforward_mono f hf ρ (hG hij)

/-- Continuity from above gives convergence in the mass of the positive
remaining tail; it supplies no quantitative convergence rate. -/
theorem filteredPushforward_tail_mass_tendsto (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) [IsFiniteMeasure ρ] (G : ℕ → Set X)
    (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G) :
    Tendsto (fun n => (filteredPushforward f ρ (G n) -
      filteredPushforward f ρ (⋂ j, G j)).real univ) atTop (𝓝 0) := by
  have hle (n : ℕ) : filteredPushforward f ρ (⋂ j, G j) ≤
      filteredPushforward f ρ (G n) :=
    filteredPushforward_mono f hf ρ (iInter_subset G n)
  have hm := tendsto_measure_iInter_atTop (μ := ρ)
    (fun n => (hG n).nullMeasurableSet) hmono ⟨0, measure_ne_top ρ _⟩
  have hr := ((ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp hm).sub_const
    ((ρ (⋂ j, G j)).toReal)
  simp only [sub_self] at hr
  convert hr using 1
  funext n
  rw [Measure.real, Measure.sub_apply MeasurableSet.univ (hle n),
    ENNReal.toReal_sub_of_le (hle n univ) (measure_ne_top _ univ),
    filteredPushforward_mass f hf, filteredPushforward_mass f hf]
  rfl

/-- Positive retained weighted mass remains positive after distance pushforward. -/
theorem filteredPushforward_positive (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G : Set X} (hG : 0 < ρ G) :
    0 < filteredPushforward f ρ G univ := by
  rwa [filteredPushforward_mass f hf]

/-- Restriction preserves the carrier of the original pushforward. -/
theorem filteredPushforward_carried (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) (G : Set X) {D : Set Y} (hD : MeasurableSet D)
    (hcarry : ρ (f ⁻¹' Dᶜ) = 0) : filteredPushforward f ρ G Dᶜ = 0 := by
  rw [filteredPushforward, Measure.map_apply hf hD.compl]
  exact le_antisymm ((Measure.restrict_apply_le G _).trans_eq hcarry) bot_le

end Falconer

end OAI
