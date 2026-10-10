import OAI.Probability.MatroidSecretary.Secretary.Model
import Mathlib.Probability.Distributions.Uniform

namespace OAI

/-! Reference-side arrival law for the actual random-prefix secretary experiment. -/
namespace MatroidProphet.Secretary
open MeasureTheory

instance uniformArrivalLaw_probability (n : ℕ) :
    IsProbabilityMeasure (uniformArrivalLaw n) := by
  unfold uniformArrivalLaw
  infer_instance

/-- Compatibility name for the source prefix set; only the analysis uses a full order. -/
abbrev prefixSet {n : ℕ} := @MatroidProphet.orderPrefix n

end MatroidProphet.Secretary

end OAI
