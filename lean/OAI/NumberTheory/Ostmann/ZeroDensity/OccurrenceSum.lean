import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualZeros

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.ZeroDensity

theorem sum_zeroOccurrences {A : Type*} [AddCommMonoid A] (Q : ℕ) (T : ℝ)
    (f : NonprincipalPrimitiveFamily Q → ℂ → A) :
    (∑ z : ZeroOccurrence Q T, f z.1 z.point) =
      ∑ χ : NonprincipalPrimitiveFamily Q,
        ∑ ρ ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset,
          Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ • f χ ρ := by
  classical
  let (χ : NonprincipalPrimitiveFamily Q) :
      Fintype {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T} :=
    (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).fintype
  change (∑ z : (Σ χ : NonprincipalPrimitiveFamily Q,
      Σ ρ : {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T},
        Fin (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ.1)), f z.1 z.2.1.1) = _
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro χ hχ
  let : Fintype {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T} := this χ
  symm
  convert Finset.sum_subtype
    (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset
    (fun ρ => (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).mem_toFinset)
    (fun ρ => Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ • f χ ρ) using 1
  swap
  · exact this
  · apply Finset.sum_congr rfl
    intro ρ hρ
    change (∑ _i : Fin (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ.1), f χ ρ.1) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem sum_retainedZeros {A : Type*} [AddCommMonoid A] (Q : ℕ)
    (exception : Option (PrimitiveFamily Q)) (σ T : ℝ)
    (f : NonprincipalPrimitiveFamily Q → ℂ → A) :
    (∑ z ∈ retainedZeros Q exception σ T, f z.1 z.point) =
      ∑ χ : NonprincipalPrimitiveFamily Q,
        ∑ ρ ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset,
          if some χ.1 ≠ exception ∧ σ ≤ ρ.re then
            Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ • f χ ρ else 0 := by
  classical
  rw [retainedZeros, Finset.sum_filter]
  have h := sum_zeroOccurrences Q T (fun χ ρ =>
    if some χ.1 ≠ exception ∧ σ ≤ ρ.re then f χ ρ else 0)
  simpa only [smul_ite, nsmul_zero] using h

end Ostmann.ZeroDensity

end

end OAI
