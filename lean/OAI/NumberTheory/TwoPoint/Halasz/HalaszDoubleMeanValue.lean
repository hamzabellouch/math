import OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentSampling
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleHolder

namespace OAI

/-! The double mean-value bound with two complete Vinogradov systems.
The explicit coordinate minimum is retained for logarithmic Taylor phases. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_double_mean_value (k M₁ M₂ r s : ℕ) (hr : 1≤r) (hs : 1≤s)
    (γ δ : Fin k → ℝ) (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j)
    (hδquarter : ∀ j,δ j≤1/4)
    (hphase : ∀ j,2*Real.pi*((r*M₁^(j.val+1):ℕ):ℝ)*δ j≤1) :
    (∏ j,δ j)^2*
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*r*s) ≤
      (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
        (halaszVinogradovCount r k M₁:ℝ)*(∏ j,2*δ j)*
          (halaszVinogradovCount s k M₂:ℝ)*
            ∏ j,min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
              (8*((s*M₂^(j.val+1):ℕ):ℝ)*δ j+
                2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*δ j/ |γ j| +2) := by
  let α : Fin M₂ → Fin k → AddCircle (1:ℝ) := fun b =>
    halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))
  let S := (univ : Finset (Fin r → Fin M₁)).image (halaszVinogradovFrequency k)
  obtain ⟨ε,hε,hd⟩ := halasz_double_holder (univ : Finset (Fin M₂)) k M₁ r s hr hs α
  have hm := halasz_moment_sampling s S ε γ δ (fun b => (hε b).le) hγ hδ hδquarter (by
    intro m hm j
    obtain ⟨x,_,rfl⟩ := mem_image.mp hm
    have hx : |(halaszVinogradovFrequency k x j:ℝ)|≤((r*M₁^(j.val+1):ℕ):ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast halasz_vinogradov_frequency_nonneg x j)]
      exact_mod_cast halasz_vinogradov_frequency_le x j
    have hpi : 0≤2*Real.pi*δ j := mul_nonneg (by positivity) (hδ j)
    nlinarith [mul_le_mul_of_nonneg_left hx hpi,hphase j])
  let C := (M₂:ℝ)^((r-1)*(2*s))*(M₁:ℝ)^(r*(2*s-2))*
    (halaszVinogradovCount r k M₁:ℝ)
  have hC : 0≤C := by dsimp only [C]; positivity
  have hd' :
      ‖∑ b : Fin M₂,halaszVinogradovPolynomial k M₁ (α b)‖^(2*r*s)≤
        C*∑ m∈S,‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s) := by
    simpa only [card_univ,Fintype.card_fin,C,S] using hd
  calc
    _ ≤ (∏ j,δ j)^2*(C*∑ m∈S,
          ‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s)) :=
      mul_le_mul_of_nonneg_left hd' (sq_nonneg _)
    _ = C*((∏ j,δ j)^2*∑ m∈S,
          ‖∑ b : Fin M₂,ε b*halaszVinogradovCharacter m (α b)‖^(2*s)) := by ring
    _ ≤ C*((∏ j,2*δ j)*(halaszVinogradovCount s k M₂:ℝ)*
          ∏ j,min (2*((s*M₂^(j.val+1):ℕ):ℝ)+1)
            (8*((s*M₂^(j.val+1):ℕ):ℝ)*δ j+
              2*((s*M₂^(j.val+1):ℕ):ℝ)* |γ j| +8*δ j/ |γ j| +2)) :=
      mul_le_mul_of_nonneg_left hm hC
    _ = _ := by dsimp only [C]; ring

end TwoPointCorrelations

end OAI
