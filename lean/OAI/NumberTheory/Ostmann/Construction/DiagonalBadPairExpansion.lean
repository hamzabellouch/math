import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairExpansionBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction
attribute [local instance] Classical.propDecidable

theorem badCounterpartPair_fixedTerm_complex (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T) → Prop)
    (hB : ∀ e, B e → PreservesRemainingBands T e)
    (G : RemainingSample sources T giant → ℝ) (A : RemainingSample sources T giant → ℂ) :
    (∑ e, if B e then ∑ x,
      ((remainingPrior sources T giant).mass x : ℂ) * (G x : ℂ) * A x *
        conj (fixedCounterpartTerm sources T giant x A e) else 0) =
    ∑ z : BadCounterpartPair sources T giant B,
      (((remainingPrior sources T giant).mass z.val.1 *
        (remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1) * G z.val.1 : ℝ) : ℂ) *
      (A z.val.1 * conj (A (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1))) := by
  rw [badCounterpartPair_sum_eq sources T giant B (fun x e hc _ =>
    (((remainingPrior sources T giant).mass x *
      (remainingPrior sources T giant).mass (reconstructCounterpart sources T giant x e hc) *
      G x : ℝ) : ℂ) * (A x * conj (A (reconstructCounterpart sources T giant x e hc))))]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : B e
  · simp only [ite_eq_left hb,dite_eq_left hb]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hc : CounterpartCompatible sources T giant x e
    · simp only [fixedCounterpartTerm,dite_eq_left hc,ite_eq_left (hB e hb),
        map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
      ring
    · simp only [fixedCounterpartTerm,dite_eq_right hc,map_zero,mul_zero]
  · simp only [ite_eq_right hb,dite_eq_right hb]

theorem badCounterpartPair_fixedTerm_re (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T) → Prop)
    (hB : ∀ e, B e → PreservesRemainingBands T e)
    (G : RemainingSample sources T giant → ℝ) (A : RemainingSample sources T giant → ℂ) :
    (∑ e, if B e then ∑ x,
      ((remainingPrior sources T giant).mass x : ℂ) * (G x : ℂ) * A x *
        conj (fixedCounterpartTerm sources T giant x A e) else 0).re =
    ∑ z : BadCounterpartPair sources T giant B,
      ((remainingPrior sources T giant).mass z.val.1 *
        (remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1) * G z.val.1) *
      (A z.val.1 * conj (A (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1))).re := by
  rw [badCounterpartPair_fixedTerm_complex sources T giant B hB G A]
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end Ostmann.Construction

end

end OAI
