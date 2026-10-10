import OAI.Combinatorics.EditApproximation.Probability.AdaptiveMarginalLaw
import OAI.Combinatorics.EditApproximation.Probability.FiniteKeyRestriction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The online draw range depends on earlier seed values. A common random
source is indexed by the physical key and the requested positive range,
not by an entire hypothetical seed table. The unused coordinates exist
only in the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory






theorem positiveDrawRangeOfLE_val (B n : ℕ) (hn : 0 < n) (hB : n ≤ B) :
    (positiveDrawRangeOfLE B n hn hB).val.val = n := rfl



abbrev CommonRangeDraw (ι : Type*) (B R : ℕ) :=
  ∀ key : CommonRangeKey ι B, Fin R → Fin key.2.val.val

noncomputable def commonRangeLaw {ι : Type*} [Fintype ι] (B R : ℕ) :
    Measure (CommonRangeDraw ι B R) :=
  Measure.pi fun key : CommonRangeKey ι B =>
    Measure.pi fun _ : Fin R => (PMF.uniformOfFintype (Fin key.2.val.val)).toMeasure

instance commonRangeLaw_probability {ι : Type*} [Fintype ι] (B R : ℕ) :
    IsProbabilityMeasure (commonRangeLaw (ι := ι) B R) := by
  unfold commonRangeLaw
  infer_instance

section Range

variable {Seed ι : Type*} [Fintype ι] (B R : ℕ) (range : Seed → ι → ℕ)
  [∀ seed key, NeZero (range seed key)] (hbounded : ∀ seed key, range seed key ≤ B)

def commonRangeSelectedKey (seed : Seed) (key : ι) : CommonRangeKey ι B :=
  (key, ⟨⟨range seed key, Nat.lt_succ_of_le (hbounded seed key)⟩, Nat.pos_of_ne_zero (NeZero.ne (range seed key))⟩)

omit [Fintype ι] in
theorem commonRangeSelectedKey_injective (seed : Seed) :
    Function.Injective (commonRangeSelectedKey B range hbounded seed) := by
  intro left right heq
  exact congrArg Prod.fst heq

def commonRangeSample (seed : Seed) (draw : CommonRangeDraw ι B R) :
    ∀ key, Fin R → Fin (range seed key) :=
  fun key => draw (commonRangeSelectedKey B range hbounded seed key)

theorem commonRangeSample_law (seed : Seed) :
    (commonRangeLaw (ι := ι) B R).map (commonRangeSample B R range hbounded seed) =
      Measure.pi fun key => Measure.pi fun _ : Fin R =>
        (PMF.uniformOfFintype (Fin (range seed key))).toMeasure := by
  have h := finite_pi_restrict_map
    (fun key : CommonRangeKey ι B => Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype (Fin key.2.val.val)).toMeasure)
    (commonRangeSelectedKey B range hbounded seed)
    (commonRangeSelectedKey_injective B range hbounded seed)
  exact h


end Range

end EditApproximation

end OAI
