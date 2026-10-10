import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementFiniteFamily

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open scoped BigOperators
open MvPolynomial
open Ostmann.Arithmetic.PolynomialFlagReplacementFinite

def independentPrimeMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (f : (ι → ℤ) → ℕ → ℂ) : ℂ :=
  ∑ x ∈ Fintype.piFinset S, ((∏ i, μ i (x i) : ℝ) : ℂ) *
    (∑ p ∈ B, (ν p : ℂ) * f x p)

theorem independentPrimeMean_flag_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℤ)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a) (hmass : ∀ i, ∑ a ∈ S i, μ i a=1)
    (hatom : ∀ i a, a ∈ S i → μ i a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ x, (∀ i, x i ∈ S i) → eval x P ≠ 0 → Real.log |((eval x P : ℤ) : ℝ)| ≤ H)
    (r : (ι → ℤ) → ℕ → Bool) (f : (ι → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ i, x i ∈ S i) → ∀ p ∈ B,
      ‖f x p‖ ≤ if r x p then A*flagError P x p else 0) :
    ‖independentPrimeMean S μ B ν f‖ ≤ A*((P.totalDegree:ℝ)*α+β*(H/Real.log 2)) := by
  have hprob := weighted_restricted_flag_error_le_all P S μ B ν α β H A
    hα hβ hH hA hμ hmass hatom hprime hν hνmass hνatom hsize r (fun _ _ => A)
    (fun _ _ _ _ => ⟨hA,le_refl _⟩)
  apply le_trans _ hprob
  unfold independentPrimeMean
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have hxs := Fintype.mem_piFinset.mp hx
  have hp : 0 ≤ ∏ i, μ i (x i) := Finset.prod_nonneg (fun i _ => hμ i _ (hxs i))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hpB
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hν p hpB)]
  exact mul_le_mul_of_nonneg_left (hf x hxs p hpB) (hν p hpB)

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
