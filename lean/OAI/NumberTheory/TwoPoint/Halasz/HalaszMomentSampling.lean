import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowPairCount
import OAI.NumberTheory.TwoPoint.Halasz.HalaszFrequencyBox

namespace OAI

/-! Fourier sampling of the second complete-system moment. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_moment_sampling {k M : ℕ} (s : ℕ) (S : Finset (Fin k → ℤ))
    (a : Fin M → ℂ) (γ δ : Fin k → ℝ) (ha : ∀ b,‖a b‖≤1)
    (hγ : ∀ j,γ j≠0) (hδ : ∀ j,0≤δ j) (hδquarter : ∀ j,δ j≤1/4)
    (hphase : ∀ m∈S,∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)^2*(∑ m∈S,
      ‖∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*s))≤
      (∏ j,2*δ j)*(halaszVinogradovCount s k M:ℝ)*
        ∏ j,min (2*((s*M^(j.val+1):ℕ):ℝ)+1)
          (8*((s*M^(j.val+1):ℕ):ℝ)*δ j+2*((s*M^(j.val+1):ℕ):ℝ)* |γ j| +
            8*δ j/ |γ j| +2) := by
  let F : (Fin s → Fin M) → Fin k → ℤ := halaszVinogradovFrequency k
  let A : (Fin s → Fin M) → ℂ := fun x => ∏ i,a (x i)
  let β : (Fin s → Fin M) → Fin k → AddCircle (1:ℝ) :=
    fun x => halaszScaledFrequency γ (F x)
  have hA (x : Fin s → Fin M) : ‖A x‖≤1 := by
    change ‖∏ i,a (x i)‖≤1
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin s,(1:ℝ) := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => ha _)
      _ = 1 := by simp
  have hh := halasz_window_sampling (univ : Finset (Fin s → Fin M)) S β A δ
    (fun x _ => hA x) hδ (fun j => (hδquarter j).trans (by norm_num)) hphase
  have hc := halasz_near_pair_count_abs F (fun j => s*M^(j.val+1)) γ δ hγ hδ hδquarter
    (fun x y j => halasz_vinogradov_difference_abs x y j)
  rw [← halasz_fiber_energy_representation,halasz_frequency_energy] at hc
  have hV : 0≤∏ j,2*δ j := prod_nonneg (fun j _ =>
    mul_nonneg (by norm_num) (hδ j))
  have hp := mul_le_mul_of_nonneg_left hc hV
  simp only [univ_product_univ] at hh
  have hs := hh.trans hp
  have he (m : Fin k → ℤ) :
      ‖∑ x : Fin s → Fin M,A x*halaszVinogradovCharacter m (β x)‖^2=
      ‖∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖^(2*s) := by
    rw [show (∑ x : Fin s → Fin M,A x*halaszVinogradovCharacter m (β x))=
      (∑ b : Fin M,a b*halaszVinogradovCharacter m
        (halaszScaledFrequency γ (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ))))^s from
      (halasz_scaled_power s γ a m).symm]
    rw [norm_pow,← pow_mul,Nat.mul_comm s 2]
  simpa only [he,mul_assoc] using hs

end TwoPointCorrelations

end OAI
