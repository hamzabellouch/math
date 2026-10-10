import OAI.NumberTheory.JointDickman.Counting.ComplexFiniteShortAverages

namespace OAI

/-! # Passing proved component short estimates to finite combinations -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory
open scoped Topology

theorem complexFiniteShort_of_components {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ℕ → ℕ → ι → ArithmeticFunction ℂ)
    (hf : ∀ B n i, i∈S → ∀ k, ‖f B n i k‖≤1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ)
    (hH : Tendsto H atTop atTop) (hX : ∀ B, Tendsto (X B) atTop atTop)
    (hcomponent : ∀ i∈S, ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/X B n)*(∫ z in X B n..2*X B n, ‖complexShortAverage (f B n i) (H B) z‖^2)<ε) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/X B n)*(∫ z in X B n..2*X B n, ‖complexFiniteShort S c (f B n) (H B) z‖^2)<ε := by
  intro ε hε
  let K := (∑ i ∈ S, ‖c i‖^2)*(S.card : ℝ)
  have hK : 0 ≤ K := mul_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  let δ := ε/(K+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall i (hi : i ∈ S) := hcomponent i hi δ hδ
  filter_upwards [(eventually_all_finset S).mpr hsmall,hH.eventually_gt_atTop 0] with B hsmall hHB
  filter_upwards [(eventually_all_finset S).mpr hsmall,(hX B).eventually_gt_atTop 0] with n hsmall hXB
  have he := complexFiniteShort_energy_le S c (f B n) (hf B n) hHB hXB
  have hs : (∑ i ∈ S, (1/X B n)*(∫ z in X B n..2*X B n,
      ‖complexShortAverage (f B n i) (H B) z‖^2)) ≤ (S.card : ℝ)*δ := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (fun i hi => (hsmall i hi).le)
  have he' := he.trans (mul_le_mul_of_nonneg_left hs (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hkδ : K*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < K+1)).mpr
    nlinarith
  exact he'.trans_lt (by simpa only [K,mul_assoc] using hkδ)


end JointDickman.PublishedInputs

end OAI
