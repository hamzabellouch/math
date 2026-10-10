import Mathlib

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory

/-- A concrete full-support probability law for every nonempty countable mark
dictionary, obtained by pushing forward a geometric law on its enumeration. -/
theorem exists_countable_full_support (I : Type) [Countable I] [Nonempty I]
    [MeasurableSpace I] [MeasurableSingletonClass I] :
    ∃ ν : Measure I, IsProbabilityMeasure ν ∧ ∀ i, 0 < ν.real {i} := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let x₀ : I := Classical.choice ‹Nonempty I›
  let f : ℕ → I := fun n => (Encodable.decode (α := I) n).getD x₀
  have hf (i : I) : f (Encodable.encode i) = i := by simp [f]
  let p : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  have hp0 : p ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  have hp1 : p ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [p] at this
  let ν := (geometricMeasure p).map f
  have hfm : Measurable f := measurable_of_countable f
  refine ⟨ν,inferInstance,?_⟩
  intro i
  have hsingle : {Encodable.encode i} ⊆ f ⁻¹' {i} := by
    intro j hj
    have hj' : j = Encodable.encode i := hj
    subst j
    exact hf i
  have hm : geometricMeasure p {Encodable.encode i} ≤ ν {i} := by
    dsimp [ν]
    rw [Measure.map_apply hfm (measurableSet_singleton i)]
    exact measure_mono hsingle
  have hpos : 0 < geometricMeasure p {Encodable.encode i} := by
    rw [geometricMeasure_singleton hp0]
    exact ENNReal.ofReal_pos.mpr (geometricMeasure_pos hp0 hp1 _)
  exact ENNReal.toReal_pos (hpos.trans_le hm).ne' (measure_ne_top ν _)

end DilutedSpinGlass
end

end

end OAI
