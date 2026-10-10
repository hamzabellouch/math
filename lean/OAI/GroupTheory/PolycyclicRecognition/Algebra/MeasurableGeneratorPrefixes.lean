import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorWordPadding
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

namespace OAI

/-! # Measurable prefixes of the fixed generator schemes

The bounded local inverse construction fixes the letter pattern. Only its
real parameters vary; hence all actual prefixes and their global logarithms
are measurable, including after an independently sampled initial suffix.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

/-- A fixed finite word with measurable real parameters has a measurable
endpoint. This includes every prefix of a bounded generator scheme. -/
theorem measurable_fixed_generator_word
    {A I G : Type*} [MeasurableSpace A] [MeasurableSpace G]
    [Group G] [MeasurableMul₂ G]
    (f : I → ℝ → G) (hf : ∀ i, Measurable (f i))
    (word : List (I × (A → ℝ))) (hw : ∀ z ∈ word, Measurable z.2) :
    Measurable (fun a => (word.map (fun z => f z.1 (z.2 a))).prod) := by
  induction word with
  | nil => simpa only [List.map_nil, List.prod_nil] using measurable_const
  | cons z word ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ((hf z.1).comp (hw z (List.mem_cons_self))).mul
        (ih (fun w hw' => hw w (List.mem_cons_of_mem _ hw')))

/-- The actual translated logarithmic prefix is measurable. A global
exponential chart provides the map `log`; no branch choice is involved. -/
theorem measurable_fixed_generator_prefix_logs
    {A I G L : Type*} [MeasurableSpace A] [MeasurableSpace G] [MeasurableSpace L]
    [Group G] [MeasurableMul₂ G]
    (f : I → ℝ → G) (hf : ∀ i, Measurable (f i))
    (word : List (I × (A → ℝ))) (hw : ∀ z ∈ word, Measurable z.2)
    (base : A → G) (hbase : Measurable base) (log : G → L) (hlog : Measurable log)
    (j : ℕ) :
    Measurable (fun a => log (base a * ((word.take j).map (fun z => f z.1 (z.2 a))).prod)) :=
  hlog.comp (hbase.mul (measurable_fixed_generator_word f hf (word.take j)
    (fun z hz => hw z (List.mem_of_mem_take hz))))

end PolycyclicRecognition

end

end OAI
