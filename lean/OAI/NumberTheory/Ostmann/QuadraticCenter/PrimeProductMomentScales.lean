import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMoment
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScalesBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_primeProduct_family_moment_bound (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, Odd p) →
      c*(Z : ℝ)/Real.log Z ≤ P.card →
      ∀ H B : ℕ, H ≤ 2*Z → B ≤ Z^14 → (∀ p ∈ P, p ≤ H) →
      ∀ S : Finset ℕ, (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, n ≤ B) →
      ∀ {α : Type} (F : Finset α) (hF : F.Nonempty), F.card ≤ Z^430 →
      ∀ (b : α → ℕ → ℂ) (U : ℝ), 0 ≤ U →
      (∀ a ∈ F, (∑ n ∈ S,
        ((((2*gridMomentParameter T : ℕ) : ℝ)^2)^n.primeFactors.card)*‖b a n‖^2) ≤ U) →
      (∀ a ∈ F, (∑ n ∈ S, ‖b a n‖) ≤ (Z : ℝ)^430) →
      let k := evenMomentParameter (parameterX T) Z
      let l := gridMomentParameter T
      primeProductMean P k (fun m =>
        (F.sup' hF (fun a => ‖∑ n ∈ S, b a n*(jacobiSym (n : ℤ) m : ℂ)‖))^(2*l)) ≤
        Real.exp (2*(l : ℝ)*ε*(auxiliaryK Z z : ℝ))*U^l+(Z : ℝ)^(-(20*(l : ℝ))) := by
  filter_upwards [eventually_primeProduct_coefficient_bounds c ε hc hε] with T hscale
  intro Z z hZl hZu hz hzl hzu P hP ho hJ H B hH hB hPH S hS hSB α F hF hFcard b U hU henergy hmass
  dsimp only
  obtain ⟨hl,hJpos,hkJ,hsquare,hnonsquare⟩ :=
    hscale Z z hZl hZu hz hzl hzu F.card H P.card B hFcard hH hJ hB
      ((Z : ℝ)^430) (by positivity) (le_refl _)
  have hmain := primeProduct_family_moment_le_factorial hP ho hJpos hkJ hPH
    S hS F hF b B hSB hl U ((Z : ℝ)^430) hU (by positivity) henergy hmass
  calc
    _ ≤ ((F.card : ℝ)*2^gridMomentParameter T*
        (((H^(evenMomentParameter (parameterX T) Z)+1 : ℕ) : ℝ)*U^gridMomentParameter T+
        (4*(B : ℝ)^(2*gridMomentParameter T))*((Z : ℝ)^430)^(2*gridMomentParameter T)))*
        (((evenMomentParameter (parameterX T) Z).factorial : ℝ)*
        (2/(P.card : ℝ))^(evenMomentParameter (parameterX T) Z)) := hmain
    _ = ((F.card : ℝ)*2^gridMomentParameter T*
        ((H : ℝ)^(evenMomentParameter (parameterX T) Z)+1)*
        ((evenMomentParameter (parameterX T) Z).factorial : ℝ)*
        (2/(P.card : ℝ))^(evenMomentParameter (parameterX T) Z))*U^gridMomentParameter T+
        (F.card : ℝ)*2^gridMomentParameter T*4*(B : ℝ)^(2*gridMomentParameter T)*
        ((Z : ℝ)^430)^(2*gridMomentParameter T)*
        ((evenMomentParameter (parameterX T) Z).factorial : ℝ)*
        (2/(P.card : ℝ))^(evenMomentParameter (parameterX T) Z) := by push_cast; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hsquare (pow_nonneg hU _)) hnonsquare

end Ostmann.QuadraticCenter

end

end OAI
