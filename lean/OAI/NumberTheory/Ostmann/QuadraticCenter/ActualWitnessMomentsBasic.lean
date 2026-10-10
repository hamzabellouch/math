import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbabilityBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

def witnessFamilyMax (F : Finset (ℕ → ℂ)) (S : Finset ℕ) (q : ℕ) : ℝ := by
  classical
  exact if h : F.Nonempty then F.sup' h (fun b => ‖∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖) else 0

theorem witnessFamilyMax_nonneg (F : Finset (ℕ → ℂ)) (S : Finset ℕ) (q : ℕ) :
    0 ≤ witnessFamilyMax F S q := by
  classical
  unfold witnessFamilyMax
  split_ifs with h
  · obtain ⟨b,hb⟩ := h
    exact (norm_nonneg (∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ))).trans (Finset.le_sup' (fun b : ℕ → ℂ => ‖∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖) hb)
  · exact le_rfl

theorem le_witnessFamilyMax {F : Finset (ℕ → ℂ)} (S : Finset ℕ) (q : ℕ)
    {b : ℕ → ℂ} (hb : b ∈ F) :
    ‖∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖ ≤ witnessFamilyMax F S q := by
  classical
  rw [witnessFamilyMax,dite_eq_left ⟨b,hb⟩]
  exact Finset.le_sup' (fun b : ℕ → ℂ => ‖∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖) hb

theorem primeProductMean_const {P : Finset ℕ} (hP : ∀p∈P,p.Prime)
    {k : ℕ} (hk : k ≤ P.card) (a : ℝ) : primeProductMean P k (fun _ => a)=a := by
  have hc : (Nat.choose P.card k:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  simp only [primeProductMean,Finset.sum_const,nsmul_eq_mul,primeProductSamples_card hP]
  exact mul_div_cancel_left₀ a hc

theorem witness_sum_le_near_family {F : Finset (ℕ → ℂ)} (S : Finset ℕ) (q : ℕ)
    (a : ℕ → ℂ) {b : ℕ → ℂ} (hb : b ∈ F) {e : ℝ}
    (he : ∑ s ∈ S,‖a s-b s‖ ≤ e) :
    ‖∑ s ∈ S,a s*(jacobiSym (s:ℤ) q:ℂ)‖ ≤ witnessFamilyMax F S q+e := by
  have herr : ‖(∑ s ∈ S,a s*(jacobiSym (s:ℤ) q:ℂ))-
      ∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖ ≤ e := by
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum _).trans he
    intro s hs
    rw [←sub_mul,norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (adaptive_jacobi_norm_le s q) (norm_nonneg (a s-b s))
  calc
    _ ≤ ‖∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖+
        ‖(∑ s ∈ S,a s*(jacobiSym (s:ℤ) q:ℂ))-
          ∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
        (∑ s ∈ S,b s*(jacobiSym (s:ℤ) q:ℂ)) (∑ s ∈ S,a s*(jacobiSym (s:ℤ) q:ℂ))
    _ ≤ _ := add_le_add (le_witnessFamilyMax S q hb) herr

theorem eventually_witnessFamilyMax_moment (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z → Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ P : Finset ℕ, (∀p∈P,p.Prime) → (∀p∈P,Odd p) →
      c*(Z:ℝ)/Real.log Z ≤ P.card → (∀p∈P,p ≤ 2*Z) →
      ∀ S : Finset ℕ, (∀s∈S,Squarefree s) → (∀s∈S,s ≤ Z^14) →
      ∀ F : Finset (ℕ → ℂ), F.card ≤ Z^430 → ∀ U : ℝ, 0 ≤ U →
      (∀b∈F,(∑s∈S,((((2*gridMomentParameter T:ℕ):ℝ)^2)^s.primeFactors.card)*‖b s‖^2) ≤ U) →
      (∀b∈F,(∑s∈S,‖b s‖) ≤ (Z:ℝ)^430) →
      primeProductMean P (evenMomentParameter (parameterX T) Z)
        (fun q => (witnessFamilyMax F S q)^(2*gridMomentParameter T)) ≤
      Real.exp (2*(gridMomentParameter T:ℝ)*ε*(auxiliaryK Z z:ℝ))*U^gridMomentParameter T+
        (Z:ℝ)^(-(20*(gridMomentParameter T:ℝ))) := by
  classical
  filter_upwards [eventually_primeProduct_family_moment_bound c ε hc hε,
    eventually_primeProduct_moment_orders] with T hm hord
  intro Z z hZl hZu hz hzl hzu P hP ho hJ hPH S hS hSB F hF U hU henergy hmass
  by_cases hne : F.Nonempty
  · simpa only [witnessFamilyMax,dite_eq_left hne] using
      hm Z z hZl hZu hz hzl hzu P hP ho hJ (2*Z) (Z^14) (le_refl _) (le_refl _)
        hPH S hS hSB F hne hF (fun b => b) U hU henergy hmass
  · have hl := (hord Z hZl hZu).1
    simp only [witnessFamilyMax,dite_eq_right hne,zero_pow (by omega : 2*gridMomentParameter T ≠ 0),
      primeProductMean,Finset.sum_const_zero,zero_div]
    positivity

end Ostmann.QuadraticCenter

end

end OAI
