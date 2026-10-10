import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoprime

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial
open scoped BigOperators

 theorem independentPrimeMean_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (f g : (ι → ℤ) → ℕ → ℂ) :
    independentPrimeMean S μ B ν (fun x p => f x p-g x p)=
      independentPrimeMean S μ B ν f-independentPrimeMean S μ B ν g := by
  simp only [independentPrimeMean,mul_sub,Finset.sum_sub_distrib]

theorem cleared_coprime_enlargement_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (P : MvPolynomial ι ℤ) (D : ℤ)
    (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ j a, a ∈ S j → 0 ≤ μ j a) (hmass : ∀ j, ∑ a ∈ S j, μ j a=1)
    (hatom : ∀ j a, a ∈ S j → μ j a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ x, (∀ j, x j ∈ S j) → eval x (eraseCoordinate i P) ≠ 0 →
      Real.log |((eval x (eraseCoordinate i P) : ℤ) : ℝ)| ≤ H)
    (r : (Other i → ℤ) → ℕ → Bool) (y : (Other i → ℤ) → ℕ → ℤ)
    (f : (Other i → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ j, x j ∈ S j) → ∀ p ∈ B, ‖f x p‖ ≤ A)
    (hclear : ∀ x, (∀ j, x j ∈ S j) → ∀ p ∈ B, r x p=true →
      D*y x p=eval (insertCoordinate i x (p:ℤ)) P)
    (hden : ∀ x, (∀ j, x j ∈ S j) → ∀ p ∈ B, r x p=true → IsCoprime (p:ℤ) D) :
    ‖independentPrimeMean S μ B ν (fun x p => coprimeSupportedValue (r x p) p (y x p) (f x p))-
      independentPrimeMean S μ B ν (fun x p => polynomialEnlargedValue (eraseCoordinate i P) (r x p) (f x p))‖ ≤
      A*(((eraseCoordinate i P).totalDegree:ℝ)*α+β*(H/Real.log 2)) := by
  classical
  rw [← independentPrimeMean_sub]
  apply independentPrimeMean_flag_bound (eraseCoordinate i P) S μ B ν α β H A
    hα hβ hH hA hμ hmass hatom hprime hν hνmass hνatom hsize r
  intro x hx p hp
  exact coprime_enlargement_pointwise i P x p (hprime p hp) D (y x p) (r x p) (f x p)
    (hf x hx p hp) (hclear x hx p hp) (hden x hx p hp)

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
