import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalEstimate
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalFamilyPoint

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial
open Ostmann.Arithmetic.PolynomialFlagReplacementFinite
open scoped BigOperators

theorem independentPrimeMean_family_flag_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset κ) (P : κ → MvPolynomial ι ℤ)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ i a, a ∈ S i → 0 ≤ μ i a) (hmass : ∀ i, ∑ a ∈ S i, μ i a=1)
    (hatom : ∀ i a, a ∈ S i → μ i a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ j ∈ D, ∀ x, (∀ i, x i ∈ S i) → eval x (P j) ≠ 0 →
      Real.log |((eval x (P j) : ℤ) : ℝ)| ≤ H)
    (r : (ι → ℤ) → ℕ → Bool) (f : (ι → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ i, x i ∈ S i) → ∀ p ∈ B,
      ‖f x p‖ ≤ if r x p then A*(∑ j ∈ D, flagError (P j) x p) else 0) :
    ‖independentPrimeMean S μ B ν f‖ ≤
      A * (∑ j ∈ D, (((P j).totalDegree : ℝ)*α+β*(H/Real.log 2))) := by
  have hprob := family_weighted_restricted_flag_error_le D P S μ B ν α β H A
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

theorem family_coprime_enlargement_error_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (D : Finset κ) (P : κ → MvPolynomial ι ℤ) (den : κ → ℤ)
    (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hμ : ∀ u a, a ∈ S u → 0 ≤ μ u a) (hmass : ∀ u, ∑ a ∈ S u, μ u a=1)
    (hatom : ∀ u a, a ∈ S u → μ u a ≤ α)
    (hprime : ∀ p ∈ B, p.Prime) (hν : ∀ p ∈ B, 0 ≤ ν p) (hνmass : ∑ p ∈ B, ν p=1)
    (hνatom : ∀ p ∈ B, ν p ≤ β)
    (hsize : ∀ j ∈ D, ∀ x, (∀ u, x u ∈ S u) → eval x (eraseCoordinate i (P j)) ≠ 0 →
      Real.log |((eval x (eraseCoordinate i (P j)) : ℤ) : ℝ)| ≤ H)
    (r : (Other i → ℤ) → ℕ → Bool) (y : κ → (Other i → ℤ) → ℕ → ℤ)
    (f : (Other i → ℤ) → ℕ → ℂ)
    (hf : ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, ‖f x p‖ ≤ A)
    (hclear : ∀ j ∈ D, ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
      den j*y j x p=eval (insertCoordinate i x (p:ℤ)) (P j))
    (hden : ∀ j ∈ D, ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true → IsCoprime (p:ℤ) (den j)) :
    ‖independentPrimeMean S μ B ν (fun x p => familyCoprimeSupportedValue D (r x p) p (fun j => y j x p) (f x p))-
      independentPrimeMean S μ B ν (fun x p => familyPolynomialEnlargedValue D
        (fun j => eraseCoordinate i (P j)) (r x p) (f x p))‖ ≤
      A * (∑ j ∈ D, (((eraseCoordinate i (P j)).totalDegree : ℝ)*α+β*(H/Real.log 2))) := by
  classical
  rw [← independentPrimeMean_sub]
  apply independentPrimeMean_family_flag_bound D (fun j => eraseCoordinate i (P j)) S μ B ν α β H A
    hα hβ hH hA hμ hmass hatom hprime hν hνmass hνatom hsize r
  intro x hx p hp
  exact family_coprime_enlargement_pointwise i D P den (fun j => y j x p) x p (hprime p hp)
    (r x p) (f x p) hA (hf x hx p hp)
    (fun j hj => hclear j hj x hx p hp) (fun j hj => hden j hj x hx p hp)

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
