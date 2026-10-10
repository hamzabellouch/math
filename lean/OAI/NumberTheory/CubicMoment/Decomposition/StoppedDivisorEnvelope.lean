import OAI.NumberTheory.CubicMoment.Estimates.DivisorLogEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.SmallBPoissonEnvelope

namespace OAI

/-! An absolute effective-frequency envelope for arbitrary coefficients.
It uses the exact quadratic energy and does not assume a prime convolution. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem arbitrary_divisor_poisson_dyad_energy (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (A N Z u : ℝ) (j : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      H ⊆ divisorFrequencyDyad d hd j →
      ‖finiteDivisorPoissonContribution d S H β u V A‖ ≤
        K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)*(2:ℝ)^j /
          (1+A*(2:ℝ)^j/(27*(norm d)^3*Z^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finiteDivisorPoissonContribution_absolute V hV hV' m
  refine ⟨72*C,by positivity,?_⟩
  intro S H β A N Z u j d hd hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hcard := primary_support_card_le S hZ.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun a => ‖β a‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : (∑ a ∈ S, ‖β a‖)^2 ≤ 18*Z*∑ a ∈ S, ‖β a‖^2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hh : (H.card:ℝ) ≤ 36*(2:ℝ)^j :=
    (show (H.card:ℝ) ≤ (frequencyDyad j).card from by
      exact_mod_cast (Finset.card_le_card hH).trans (divisorFrequencyDyad_card_le d hd j)).trans
        (frequencyDyad_card_le j)
  have hb := hbound A N Z ((2:ℝ)^j/norm d) hA hN hNZ (by positivity) d hd S H hS
    (fun h hh => (divisorFrequencyDyad_norm (hH hh)).1) β u
  have heq : (A/(norm d)^2)*((2:ℝ)^j/norm d)/(27*Z^2) =
      A*(2:ℝ)^j/(27*(norm d)^3*Z^2) := by ring
  rw [heq] at hb
  calc
    _ ≤ C*((A/(norm d)^2)/(9*N))*(36*(2:ℝ)^j)*
        (18*Z*∑ a ∈ S, ‖β a‖^2)/(1+A*(2:ℝ)^j/(27*(norm d)^3*Z^2))^m := by
      apply hb.trans
      gcongr
    _ = _ := by ring

theorem arbitrary_divisor_poisson_energy_tail (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      let t := A/(27*(norm d)^3*Z^2)
      Summable (fun j => finiteDivisorPoissonContribution d S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d S (H (j+n)) β u V A‖ ≤
        (K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_divisor_poisson_dyad_energy V hV hV' (m+3)
  refine ⟨K,hK,?_⟩
  intro S H β A N Z u n d hd hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  let t := A/(27*(norm d)^3*Z^2)
  let E := K*((A/(norm d)^2)/N)*Z*∑ a ∈ S, ‖β a‖^2
  have ht : 0 < t := by dsimp [t]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrow (j : ℕ) : ‖finiteDivisorPoissonContribution d S (H j) β u V A‖ ≤
      E*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have he : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*(norm d)^3*Z^2) := by dsimp [t]; ring
    dsimp only [E]
    rw [he]
    exact hbound S (H j) β A N Z u j d hd hA hN hNZ hS (hH j)
  exact poisson_dyadic_tail ht hE m n
    (fun j => finiteDivisorPoissonContribution d S (H j) β u V A) hrow

end CubicFirstMoment

end

end OAI
