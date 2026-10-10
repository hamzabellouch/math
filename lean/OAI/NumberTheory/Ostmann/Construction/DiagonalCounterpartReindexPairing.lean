import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBijection

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

theorem remainingDiagonal_eq_counterpart_pairing (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      (∑x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
        ∑v : AllowedFrequency V l,
          ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x:ℂ)*
          remainingIntegrand d P sources seed V giant X G bins outside l p u x v *
          conj (∑y,if remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y=
            remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x then
              ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass y:ℂ)*
                remainingIntegrand d P sources seed V giant X G bins outside l p u y v else 0)).re := by
  rw [remainingDiagonal_eq_product_diagonal_of_positive_mass d P sources seed V giant X G bins outside l p u hg hs]
  apply congrArg Complex.re
  simp only [refinedRowDiagonal,diagonalComplex,Fintype.sum_prod_type,
    remainingTermMass,remainingTermProductTag,remainingTermValue,Prod.mk.injEq,Subtype.val_inj]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro xs hxs
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  by_cases he : remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant (r,ys)=
      remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant (q,xs)
  · simp [he]
  · simp [he]

theorem remainingDiagonal_eq_counterpart_permutations (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      (∑x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant,
        ∑v : AllowedFrequency V l,
          if remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0 then
          ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x:ℂ)*
          remainingIntegrand d P sources seed V giant X G bins outside l p u x v *
          conj (∑e : CounterpartPermutation sources (Template.remainder (l+1) (Template.current seed l)) giant x,
            let y := reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant x e.val e.property
            ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass y:ℂ)*
              remainingIntegrand d P sources seed V giant X G bins outside l p u y v) else 0).re := by
  rw [remainingDiagonal_eq_counterpart_pairing d P sources seed V giant X G bins outside l p u hg hs]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hf : remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0
  · rw [ite_eq_left hf,weighted_remainingProduct_eq_counterparts sources _ giant x
      (remainingValues_nodup_of_integrand_ne_zero d P sources seed V giant X G bins outside l p u x v hf)]
  · simp only [not_not] at hf
    simp [hf]

end Ostmann.Construction

end

end OAI
