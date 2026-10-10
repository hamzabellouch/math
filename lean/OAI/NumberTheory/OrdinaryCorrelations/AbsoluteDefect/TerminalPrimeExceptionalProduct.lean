import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellin
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCoefficientEnergy

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryCorrelations OrdinarySparseLargeValues OrdinaryDirichletMeanSquare
open Finset Filter

theorem terminal_prime_exceptional_product {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀ p∈P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∀ᶠ H : ℕ in atTop,
      ∀ (N k : ℕ) (V : ℝ), 2 ≤ N → 4*r ≤ k → 0 < V →
      (2*(N:ℝ))^k ≤ (H:ℝ) → (H:ℝ) ≤ (2*(N:ℝ))^(k+1) →
      (2*momentBase k)^(8*r) ≤ (N:ℝ) → 1 ≤ (N:ℝ)*V^(8*r) →
      ∀ A : Finset ℕ, (∀ p∈A, Nat.Prime p) → A ⊆ Ioc N (2*N) →
      ∀ T : Finset ℝ, (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) →
      (∀ t∈T, |t| ≤ (H:ℝ)) →
      (∑ t ∈ T.filter (fun t => V ≤ ‖primeMellin f χ A t‖),
        ‖primeMellin f χ P t * dyadicCofactorMellin f χ P (2*H) t‖^2) < ε := by
  classical
  obtain ⟨r,hr,hevent⟩ := terminal_product_sparse hf hm hNP hq χ P hP hε
  refine ⟨r,hr,?_⟩
  filter_upwards [hevent,eventually_ge_atTop 1] with H hH hH1
  intro N k V hN hk hV hlower hupper hsize hthreshold A hA hband T hsep hheight
  let S := T.filter (fun t => V ≤ ‖primeMellin f χ A t‖)
  have hS : S ⊆ T := filter_subset _ _
  have hsepS : (S : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|) :=
    hsep.mono (by exact_mod_cast hS)
  have hheightS : ∀ t∈S, |t| ≤ (H:ℝ) := fun t ht => hheight t (hS ht)
  have hcard := dyadic_prime_large_values_sparse hN (by exact_mod_cast hH1)
    hV hr hk hlower hupper hsize hthreshold A hA hband
    (fun p => characterModulation f χ p/(p:ℂ))
    (fun p hp => prime_coefficient_norm hf χ p) S hheightS hsepS
    (fun t ht => (mem_filter.mp ht).2)
  exact hH S hsepS hheightS (by exact_mod_cast hcard)

end SourcePrimeFactor

end

end OAI
