import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexCoefficient
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexPairing

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

def bandCounterpartSum (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) (F : RemainingSample sources T giant→ℂ) : ℂ :=
  ∑e : CounterpartPermutation sources T giant x,
    if PreservesRemainingBands T e.val then
      let y := reconstructCounterpart sources T giant x e.val e.property
      ((remainingPrior sources T giant).mass y:ℂ)*F y else 0

theorem remainingDiagonal_eq_band_counterpart_pairing (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l))
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      (∑x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
        ∑v : AllowedFrequency V l,
          ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x:ℂ)*
          remainingIntegrand d P sources seed V giant X G bins outside l p u x v *
          conj (bandCounterpartSum sources (Template.remainder (l+1) (Template.current seed l)) giant x
            (fun y => remainingIntegrand d P sources seed V giant X G bins outside l p u y v))).re := by
  rw [remainingDiagonal_eq_counterpart_pairing d P sources seed V giant X G bins outside l p u hg hs]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hfx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v=0
  · simp only [hfx,mul_zero,zero_mul]
  by_cases hmx : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x=0
  · simp only [hmx,Complex.ofReal_zero,zero_mul]
  rw [weighted_remainingProduct_eq_band_counterparts sources _ giant hsep x
    (remainingValues_nodup_of_integrand_ne_zero d P sources seed V giant X G bins outside l p u x v hfx) hmx]
  rfl

theorem actualCoefficient_counterpart_sum (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ) (g : ∀q : ℕ,ZMod q→ℂ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : ℤ)
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (hmx : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0)
    (hfx : actualCoefficient sources seed V X G g bins outside l
      (remainingState sources (Template.current seed l) (l+1) giant p u x v)≠0) :
    (∑y,if remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y=
        remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x then
      ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass y:ℂ)*
      actualCoefficient sources seed V X G g bins outside l
        (remainingState sources (Template.current seed l) (l+1) giant p u y v) else 0) =
    bandCounterpartSum sources (Template.remainder (l+1) (Template.current seed l)) giant x
      (fun y => actualCoefficient sources seed V X G g bins outside l
        (remainingState sources (Template.current seed l) (l+1) giant p u y v)) :=
  weighted_remainingProduct_eq_band_counterparts sources _ giant hsep x
    (remainingValues_nodup_of_actualCoefficient_ne_zero sources seed V giant X G g bins outside l p u x v hfx) hmx _

end Ostmann.Construction

end

end OAI
