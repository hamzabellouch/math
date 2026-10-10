import OAI.NumberTheory.CubicMoment.Estimates.PoissonAbsoluteDyad
import OAI.NumberTheory.CubicMoment.Estimates.QuantitativeNoncube
import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailSum

namespace OAI

/-! An absolute Poisson envelope and its actual infinite tail for
arbitrary coefficients, in terms of their exact quadratic energy. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem arbitrary_poisson_dyad_energy (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (A N Z u : ℝ) (j : ℕ), 0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) → H ⊆ frequencyDyad j →
      ‖finitePoissonContribution S H β u V A‖ ≤
        K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)*(2:ℝ)^j/(1+A*(2:ℝ)^j/(27*Z^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finitePoissonContribution_absolute V hV hV' m
  refine ⟨72*C,by positivity,?_⟩
  intro S H β A N Z u j hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hcard := primary_support_card_le S hZ.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun a => ‖β a‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : (∑ a ∈ S, ‖β a‖)^2 ≤ 18*Z*∑ a ∈ S, ‖β a‖^2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hh : (H.card:ℝ) ≤ 36*(2:ℝ)^j :=
    (show (H.card:ℝ) ≤ (frequencyDyad j).card from by exact_mod_cast Finset.card_le_card hH).trans
      (frequencyDyad_card_le j)
  have hb := hbound A N Z ((2:ℝ)^j) hA hN hNZ (by positivity) S H hS
    (fun h hmem => (frequencyDyad_norm (hH hmem)).1) β u
  calc
    _ ≤ C*(A/(9*N))*(36*(2:ℝ)^j)*(18*Z*∑ a ∈ S, ‖β a‖^2)/
        (1+A*(2:ℝ)^j/(27*Z^2))^m := by
      apply hb.trans
      gcongr
    _ = _ := by ring

theorem arbitrary_poisson_energy_tail (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ), 0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ frequencyDyad j) →
      let t := A/(27*Z^2)
      Summable (fun j => finitePoissonContribution S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution S (H (j+n)) β u V A‖ ≤
        (K*(A/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_poisson_dyad_energy V hV hV' (m+3)
  refine ⟨K,hK,?_⟩
  intro S H β A N Z u n hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  let t := A/(27*Z^2)
  let E := K*(A/N)*Z*∑ a ∈ S, ‖β a‖^2
  have ht : 0 < t := by dsimp [t]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hr (j : ℕ) : ‖finitePoissonContribution S (H j) β u V A‖ ≤
      E*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have he : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*Z^2) := by dsimp [t]; ring
    dsimp only [E]
    rw [he]
    exact hbound S (H j) β A N Z u j hA hN hNZ hS (hH j)
  exact poisson_dyadic_tail ht hE m n
    (fun j => finitePoissonContribution S (H j) β u V A) hr

end CubicFirstMoment

end

end OAI
