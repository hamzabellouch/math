import OAI.NumberTheory.TwoPoint.Halasz.HalaszWindowOverlap

namespace OAI

/-! A finite sampling inequality from the compact coefficient-torus window.
The right side counts actual nearby pairs of sampling centers. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical ComplexConjugate

lemma halasz_character_window_inner {k : ℕ} (δ : Fin k → ℝ)
    (m : Fin k → ℤ) (β : Fin k → AddCircle (1:ℝ)) :
    inner ℂ (halaszCharacterL2 m) (halaszWindowL2 δ β)=
      halaszVinogradovCharacter m β*
        ∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
          ∂halaszVinogradovHaar k := by
  rw [L2.inner_def]
  have he : (∫ α,inner ℂ (halaszCharacterL2 m α) (halaszWindowL2 δ β α)
      ∂halaszVinogradovHaar k)=
      ∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ (α+β)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_character_l2_coe m,halasz_window_l2_coe δ β] with α hm hb
    rw [hm,hb]
    simp only [RCLike.inner_apply']
  rw [he,halasz_torus_fourier_translation]

/-- Finite Fourier sampling costs only the volume of the window times the
number of pairs of centers whose translated windows can meet. -/
theorem halasz_window_sampling {ι : Type*} {k : ℕ}
    (B : Finset ι) (S : Finset (Fin k → ℤ))
    (β : ι → Fin k → AddCircle (1:ℝ)) (a : ι → ℂ) (δ : Fin k → ℝ)
    (ha : ∀ b∈B,‖a b‖≤1) (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (hphase : ∀ m∈S,∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)^2*(∑ m∈S,‖∑ b∈B,a b*halaszVinogradovCharacter m (β b)‖^2)≤
      (∏ j,2*δ j)*
        (((B×ˢB).filter (fun p => HalaszWindowNear δ (β p.1) (β p.2))).card:ℝ) := by
  let u := ∑ b∈B,a b • halaszWindowL2 δ (β b)
  have he (m : Fin k → ℤ) : inner ℂ (halaszCharacterL2 m) u=
      (∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
        ∂halaszVinogradovHaar k)*
      (∑ b∈B,a b*halaszVinogradovCharacter m (β b)) := by
    simp only [u,inner_sum,inner_smul_right,halasz_character_window_inner,mul_sum]
    apply sum_congr rfl
    intro b _
    ring
  have hb := mrt_gram_analysis S halaszCharacterL2 u (B := 1) (by norm_num)
    (fun m hm => by
      simp only [halasz_character_l2_inner,apply_ite norm,norm_one,norm_zero]
      simp [hm])
  have hs := halasz_synthesis_overlap B (fun b => halaszWindowL2 δ (β b)) a
    (fun b c => HalaszWindowNear δ (β b) (β c)) ha
    (fun b _ c _ => halasz_window_l2_overlap δ hδ hδhalf (β b) (β c))
  apply le_trans _ (hb.trans (by simpa only [one_mul] using hs))
  rw [mul_sum]
  apply sum_le_sum
  intro m hm
  rw [he,norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (prod_nonneg (fun j _ => hδ j))
    (halasz_torus_window_coefficient δ m hδ hδhalf (hphase m hm)) 2

end TwoPointCorrelations

end OAI
