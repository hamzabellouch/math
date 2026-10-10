import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableFirstDefault
import OAI.MeasureTheory.DyadicAvoidance.ConcreteLabelMeasures

namespace OAI

universe u_T

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem310.FiniteTableModel

/-- Center-table coordinate in the bounded-address convention used by the
first-default probability theorem. -/
def centerTableAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ)
    (a : FirstDefault.BoundedAddress M d) : SelectorAddress b :=
  selectorAddress b ⟨a.1.1, a.2⟩ a.1.2 x

lemma centerTableAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ) (x : ℝ) :
    Function.Injective (centerTableAddress b x) := by
  intro a c h
  have hp := congrArg Sigma.fst h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Node M d × Fin M => z.1.val) hp
  · exact congrArg (fun z : Node M d × Fin M => z.2) hp

/-- Exact no-default probability for the canonical spatial selector tables,
at every real center and every choice of deterministic grid resolutions. -/
theorem measure_center_no_default {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    (Measure.pi (fun _ : SelectorAddress b => ν))
      (⋃ f : FirstDefault.Path M d, {ω | ∀ i : FirstDefault.Tests f,
        selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  have h := FirstDefault.measure_no_default_finite_table ν hfair
    (centerTableAddress b x) (centerTableAddress_injective b x)
  simpa only [centerTableAddress, FirstDefault.boundedAddress,
    selectorValue, dite_eq_left (FirstDefault.address_length_lt _ _)] using h

/-- Adding the independent terminal tables does not change the center-path
survival probability. This is the full outcome-space form used by repair. -/
theorem measure_center_no_default_prod {M d : ℕ}
    {T : Type u_T} [MeasurableSpace T] (τ : Measure T) [IsProbabilityMeasure τ]
    (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    ((Measure.pi (fun _ : SelectorAddress b => ν)).prod τ)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  let E : Set (SelectorTable b) := ⋃ f : FirstDefault.Path M d,
    {ω | ∀ i : FirstDefault.Tests f,
      selectorValue b ω (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
        FirstDefault.requiredBit f i}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have heq : (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) = Prod.fst ⁻¹' E := by
    ext ω
    simp only [E, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [heq, measurePreserving_fst.measure_preimage hE.nullMeasurableSet]
  exact measure_center_no_default b ν hfair x

/-- The survival estimate with all probability measures instantiated, including
the Bernoulli terminal labels in the canonical complete outcome space. -/
theorem outcomeLaw_center_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable bS × TerminalTable bT |
        ∀ i : FirstDefault.Tests f,
        selectorValue bS ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by
  exact measure_center_no_default_prod
    (ConcreteLabels.terminalLaw (TerminalAddress bT) p hp0 hp1)
    bS ConcreteLabels.fairLaw ConcreteLabels.fairLaw_singleton x

end Problem310.FiniteTableModel

end

end OAI
