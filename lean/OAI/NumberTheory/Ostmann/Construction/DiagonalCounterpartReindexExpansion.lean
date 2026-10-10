import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindex
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransform

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

theorem grouped_multiplier_expansion {α κ : Type*} [Fintype α] [DecidableEq κ]
    (tag : α→κ) (f : α→ℂ) (M : α→ℝ) (tags : Finset κ) (rep : ↥tags→α)
    (hcover : ∀x,f x≠0→tag x∈tags)
    (hM : ∀t : ↥tags,∀x,tag x=t.val→f x≠0→M x=M (rep t)) :
    ((∑t : ↥tags,M (rep t)*‖groupedValue Finset.univ tag f t.val‖^2:ℝ):ℂ)=
      ∑x,(M x:ℂ)*f x*conj (groupedValue Finset.univ tag f (tag x)) := by
  have ht (t : ↥tags) : (M (rep t):ℂ)*(‖groupedValue Finset.univ tag f t.val‖^2:ℝ)=
      ∑x,if tag x=t.val then (M x:ℂ)*f x*conj (groupedValue Finset.univ tag f t.val) else 0 := by
    rw [Complex.ofReal_pow,←Complex.mul_conj']
    conv_lhs => arg 2; arg 1; unfold groupedValue
    rw [Finset.sum_mul,Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases he : tag x=t.val
    · by_cases hf : f x=0
      · simp [he,hf]
      · simp only [he,ite_true,hM t x he hf]
        ring
    · simp [he]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hf : f x=0
  · simp [hf]
  let t : ↥tags := ⟨tag x,hcover x hf⟩
  rw [Finset.sum_eq_single t]
  · simp [t]
  · intro b hb hbt
    have hn : tag x≠b.val := by
      intro he
      exact hbt (Subtype.ext he.symm)
    simp [hn]
  · simp

theorem diagonal_grouped_coefficient_eq_counterpart (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l) :
    groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z)
      (remainingTermProductTag sources seed V giant l (x,v)) =
    ∑y,if remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant y=
        remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x then
      ((remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass y:ℂ)*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (y,v) else 0 := by
  simp only [groupedValue,Finset.sum_filter,Fintype.sum_prod_type,
    remainingTermProductTag,remainingTermMass,Prod.mk.injEq,Subtype.val_inj]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro ys hys
  by_cases he : remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant (q,ys)=
      remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant x
  · simp [he]
  · simp [he]

theorem diagonal_grouped_coefficient_eq_band_counterpart (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l)
    (hsep : RemainingBandsSeparated sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (hmx : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0)
    (hA : diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v)≠0) :
    groupedValue Finset.univ (remainingTermProductTag sources seed V giant l)
      (fun z => (remainingTermMass sources seed V giant l z:ℂ)*
        diagonalCoefficientTerm d sources seed V giant X G bins outside l p u z)
      (remainingTermProductTag sources seed V giant l (x,v)) =
      bandCounterpartSum sources (Template.remainder (l+1) (Template.current seed l)) giant x
        (fun y => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (y,v)) := by
  rw [diagonal_grouped_coefficient_eq_counterpart d sources seed V giant X G bins outside l p u x v]
  exact actualCoefficient_counterpart_sum sources seed V giant X G (residueTransform d) bins outside l p u
    x v.val hsep hmx hA

end Ostmann.Construction

end

end OAI
