import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableShannonInformation

namespace OAI

/-! # Encoding a countable observation preserves its Shannon sum -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree

lemma encoded_observation_information
    {Y α : Type*} [MeasurableSpace Y] [Encodable α]
    (μ : Measure Y) (P : Y → α) :
    (Summable (fun n : ℕ => Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})) ↔
      Summable (fun a : α => Real.negMulLog (μ.real {x | P x=a}))) ∧
    (∑' n : ℕ, Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})) =
      ∑' a : α, Real.negMulLog (μ.real {x | P x=a}) := by
  classical
  let f : ℕ → ℝ := fun n => Real.negMulLog (μ.real {x | Encodable.encode (P x)=n})
  have hout (n : ℕ) (hn : n ∉ range (Encodable.encode : α → ℕ)) : f n=0 := by
    have he : {x | Encodable.encode (P x)=n}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hn ⟨P x,hx⟩
    simp only [f,he,measureReal_empty,Real.negMulLog_zero]
  have he (a : α) : f (Encodable.encode a)=Real.negMulLog (μ.real {x | P x=a}) := by
    have hh : {x | Encodable.encode (P x)=Encodable.encode a}={x | P x=a} := by
      ext x
      exact Encodable.encode_injective.eq_iff
    change Real.negMulLog (μ.real {x | Encodable.encode (P x)=Encodable.encode a}) = _
    rw [hh]
  constructor
  · have h := Encodable.encode_injective.summable_iff hout
    simpa only [Function.comp_def,he] using h.symm
  · have h := Encodable.encode_injective.tsum_eq (f := f) (by
      intro n hn
      by_contra hnot
      exact hn (hout n hnot))
    simpa only [he] using h.symm

end DukePrimeDegree

end

end OAI
