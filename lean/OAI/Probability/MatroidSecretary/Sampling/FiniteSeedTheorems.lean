import OAI.Probability.MatroidSecretary.Sampling.FiniteSeedModel
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

namespace OAI

/-! Exact finite-seed encoding, measurability, and law preservation. -/

open MeasureTheory
namespace MatroidProphet

variable (α : Type*) [Fintype α]

lemma finiteSeedEncode_injective : Function.Injective (finiteSeedEncode α) := by
  classical
  intro a b h
  have hb : finiteSeedEncode α b ((Fintype.equivFin α) a) = true := by
    rw [← h]
    simp [finiteSeedEncode]
  have he : (Fintype.equivFin α) b = (Fintype.equivFin α) a := by
    simpa [finiteSeedEncode] using hb
  exact (Fintype.equivFin α).injective he.symm

variable [Nonempty α]

@[simp] lemma finiteSeedDecode_encode (a : α) :
    finiteSeedDecode α (finiteSeedEncode α a) = a := by
  exact Function.leftInverse_invFun (finiteSeedEncode_injective α) a

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Nonempty α] in
lemma measurable_finiteSeedEncode : Measurable (finiteSeedEncode α) :=
  measurable_of_finite _

omit [MeasurableSingletonClass α] in
lemma measurable_finiteSeedDecode : Measurable (finiteSeedDecode α) :=
  measurable_of_finite _

/-- The full original law is recovered, not merely the law of a used statistic. -/
theorem finiteSeed_map_roundtrip (μ : Measure α) :
    (μ.map (finiteSeedEncode α)).map (finiteSeedDecode α) = μ := by
  rw [Measure.map_map (measurable_finiteSeedDecode α) (measurable_finiteSeedEncode α)]
  simp only [Function.comp_def, finiteSeedDecode_encode]
  exact Measure.map_id

/-- Decoding the encoded law preserves every event of the original seed. -/
theorem finiteSeed_decode_measurePreserving (μ : Measure α) :
    MeasurePreserving (finiteSeedDecode α) (μ.map (finiteSeedEncode α)) μ :=
  ⟨measurable_finiteSeedDecode α, finiteSeed_map_roundtrip α μ⟩

/-- Arbitrary real payoff statistics have exactly the same expectation. -/
theorem finiteSeed_integral_decode (μ : Measure α) (g : α → ℝ) :
    (∫ r, g (finiteSeedDecode α r) ∂μ.map (finiteSeedEncode α)) = ∫ a, g a ∂μ := by
  have h := integral_map_of_stronglyMeasurable (μ := μ)
    (measurable_finiteSeedEncode α)
    ((measurable_of_finite (fun r => g (finiteSeedDecode α r))).stronglyMeasurable)
  simpa only [finiteSeedDecode_encode] using h

/-- Encoding a full seed does not change its independence from any other data. -/
theorem finiteSeed_indepFun_iff {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (X : Ω → β) (R : Ω → α) :
    ProbabilityTheory.IndepFun X (finiteSeedEncode α ∘ R) μ ↔
      ProbabilityTheory.IndepFun X R μ := by
  constructor
  · intro h
    have hd := h.comp measurable_id (measurable_finiteSeedDecode α)
    simpa only [Function.comp_def, id_eq, finiteSeedDecode_encode] using hd
  · intro h
    simpa only [Function.comp_def, id_eq] using
      h.comp measurable_id (measurable_finiteSeedEncode α)

section Reindex

variable {n bits bits' : ℕ} (A : OnlineRule n bits) (f : Seed bits' → Seed bits)

@[simp] theorem reindexOnlineSeed_decisionAt (r : Seed bits') (s v : Weights n)
    (π : ArrivalOrder n) (k : Fin n) :
    decisionAt (reindexOnlineSeed A f) r s v π k = decisionAt A (f r) s v π k := rfl

@[simp] theorem reindexOnlineSeed_acceptedThrough (r : Seed bits') (s v : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (reindexOnlineSeed A f) r s v π t =
      acceptedThrough A (f r) s v π t := rfl

@[simp] theorem reindexOnlineSeed_reward (r : Seed bits') (s v : Weights n)
    (π : ArrivalOrder n) :
    reward (reindexOnlineSeed A f) r s v π = reward A (f r) s v π := rfl

/-- Total decoding also preserves feasibility on encodings outside the support. -/
theorem reindexOnlineSeed_feasible (M : Matroid (Fin n)) (hA : Feasible M A) :
    Feasible M (reindexOnlineSeed A f) := by
  intro r s v π t hs hv
  exact hA (f r) s v π t hs hv

variable (H : HiddenRule n bits)

@[simp] theorem reindexHiddenSeed_acceptedThrough (r : Seed bits') (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (reindexHiddenSeed H f) r w π t =
      hiddenAcceptedThrough H (f r) w π t := rfl

@[simp] theorem reindexHiddenSeed_reward (r : Seed bits') (w : Weights n)
    (π : ArrivalOrder n) :
    hiddenReward (reindexHiddenSeed H f) r w π = hiddenReward H (f r) w π := rfl

@[simp] theorem reindexHiddenSeed_worstReward (r : Seed bits') (w : Weights n) :
    hiddenWorstReward (reindexHiddenSeed H f) w r = hiddenWorstReward H w (f r) := rfl

/-- No independence of the adversary from the reindexed seed is used. -/
theorem reindexHiddenSeed_integral (ν' : Measure (Seed bits'))
    (ν : Measure (Seed bits)) (hlaw : ν'.map f = ν) (w : Weights n) :
    (∫ r, hiddenWorstReward (reindexHiddenSeed H f) w r ∂ν') =
      ∫ r, hiddenWorstReward H w r ∂ν := by
  rw [← hlaw]
  exact (integral_map_of_stronglyMeasurable (μ := ν')
    (measurable_of_finite f)
    (measurable_of_finite (hiddenWorstReward H w)).stronglyMeasurable).symm

end Reindex

end MatroidProphet

end OAI
