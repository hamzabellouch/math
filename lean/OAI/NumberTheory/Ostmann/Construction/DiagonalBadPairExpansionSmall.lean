import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairExpansion
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexFinal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction
attribute [local instance] Classical.propDecidable

theorem badCounterpartPair_fixedTerm_sum_re {J : Type*} [Fintype J]
    (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (B : Equiv.Perm (RemainingIndex T) → Prop) (hB : ∀ e, B e → PreservesRemainingBands T e)
    (G : RemainingSample sources T giant → J → ℝ)
    (A : RemainingSample sources T giant → J → ℂ) :
    (∑ e, if B e then ∑ x, ∑ v : J,
      ((remainingPrior sources T giant).mass x : ℂ) * (G x v : ℂ) * A x v *
        conj (fixedCounterpartTerm sources T giant x (fun y => A y v) e) else 0).re =
    ∑ v : J, ∑ z : BadCounterpartPair sources T giant B,
      ((remainingPrior sources T giant).mass z.val.1 *
        (remainingPrior sources T giant).mass
          (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1) * G z.val.1 v) *
      (A z.val.1 v * conj (A (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1) v)).re := by
  let f := fun (e : Equiv.Perm (RemainingIndex T)) (x : RemainingSample sources T giant) (v : J) =>
    ((remainingPrior sources T giant).mass x : ℂ) * (G x v : ℂ) * A x v *
      conj (fixedCounterpartTerm sources T giant x (fun y => A y v) e)
  have he : (∑ e, if B e then ∑ x, ∑ v : J, f e x v else 0) =
      ∑ v : J, ∑ e, if B e then ∑ x, f e x v else 0 := by
    calc
      _ = ∑ e, ∑ v : J, if B e then ∑ x, f e x v else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hb : B e
        · simp only [ite_eq_left hb]
          exact Finset.sum_comm
        · simp only [ite_eq_right hb,Finset.sum_const_zero]
      _ = _ := Finset.sum_comm
  change (∑ e, if B e then ∑ x, ∑ v : J, f e x v else 0).re = _
  rw [he,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact badCounterpartPair_fixedTerm_re sources T giant B hB (fun x => G x v) (fun x => A x v)

theorem fixedSmallCounterpartExpression_badPair_re
    (d : Decomposition) (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant : PrimeSource) (X G : ℝ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (B : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))) → Prop)
    (hB : ∀ e, B e → PreservesRemainingBands (Template.remainder (l+1) (Template.current seed l)) e) :
    (∑ e, if B e then fixedSmallCounterpartExpression d sources seed V giant X G bins outside l p u e
      else 0).re =
    ∑ v : AllowedFrequency V l,
      ∑ z : BadCounterpartPair sources (Template.remainder (l+1) (Template.current seed l)) giant B,
        ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass z.val.1 *
          (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass
            (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant
              z.val.1 z.val.2 z.property.1) *
          diagonalSmallTerm d sources seed V giant outside l p u (z.val.1,v)) *
        (diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (z.val.1,v) *
          conj (diagonalCoefficientTerm d sources seed V giant X G bins outside l p u
            (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant
              z.val.1 z.val.2 z.property.1,v))).re := by
  exact badCounterpartPair_fixedTerm_sum_re sources
    (Template.remainder (l+1) (Template.current seed l)) giant B hB
    (fun x v => diagonalSmallTerm d sources seed V giant outside l p u (x,v))
    (fun x v => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v))

end Ostmann.Construction

end

end OAI
