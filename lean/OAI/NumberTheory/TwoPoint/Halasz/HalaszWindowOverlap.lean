import OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusWindow
import OAI.NumberTheory.TwoPoint.Halasz.HalaszOverlapSynthesis

namespace OAI

/-! Translated product windows only interact at nearby centers. -/
namespace TwoPointCorrelations

open MeasureTheory Finset Set Metric
open scoped Classical ComplexConjugate

def HalaszWindowNear {k : ℕ} (δ : Fin k → ℝ)
    (β γ : Fin k → AddCircle (1:ℝ)) : Prop := ∀ j, ‖β j-γ j‖≤2*δ j

lemma halasz_window_common_near {k : ℕ} (δ : Fin k → ℝ)
    (α β γ : Fin k → AddCircle (1:ℝ))
    (hβ : α+β∈Set.univ.pi (fun j => closedBall 0 (δ j)))
    (hγ : α+γ∈Set.univ.pi (fun j => closedBall 0 (δ j))) :
    HalaszWindowNear δ β γ := by
  intro j
  have hb : ‖α j+β j‖≤δ j := by
    simpa only [mem_closedBall,dist_zero_right,Pi.add_apply] using hβ j (mem_univ j)
  have hc : ‖α j+γ j‖≤δ j := by
    simpa only [mem_closedBall,dist_zero_right,Pi.add_apply] using hγ j (mem_univ j)
  calc
    _ = ‖(α j+β j)-(α j+γ j)‖ := by congr 1; abel
    _ ≤ ‖α j+β j‖+‖α j+γ j‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma halasz_window_product_bound {k : ℕ} (δ : Fin k → ℝ)
    (α β γ : Fin k → AddCircle (1:ℝ)) :
    ‖conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)‖≤
      if HalaszWindowNear δ β γ then ‖halaszTorusWindow δ (α+β)‖^2 else 0 := by
  by_cases hb : α+β∈Set.univ.pi (fun j => closedBall 0 (δ j))
  · by_cases hc : α+γ∈Set.univ.pi (fun j => closedBall 0 (δ j))
    · have hn := halasz_window_common_near δ α β γ hb hc
      simp [halaszTorusWindow,hb,hc,hn]
    · simp only [halaszTorusWindow,indicator_of_mem hb,indicator_of_notMem hc,
        mul_zero,norm_zero,norm_one,one_pow]
      split_ifs <;> norm_num
  · simp [halaszTorusWindow,hb]

lemma halasz_window_translate_memLp {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) :
    MemLp (fun α => halaszTorusWindow δ (α+β)) 2 (halaszVinogradovHaar k) := by
  have : (halaszVinogradovHaar k).IsAddRightInvariant := by
    unfold halaszVinogradovHaar
    infer_instance
  exact (halasz_torus_window_memLp δ).comp_measurePreserving
    (measurePreserving_add_right (halaszVinogradovHaar k) β)

lemma halasz_window_overlap_integral {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (β γ : Fin k → AddCircle (1:ℝ)) :
    ‖∫ α,conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)
      ∂halaszVinogradovHaar k‖≤
      if HalaszWindowNear δ β γ then ∏ j,2*δ j else 0 := by
  apply (norm_integral_le_integral_norm _).trans
  by_cases hn : HalaszWindowNear δ β γ
  · rw [ite_eq_left hn]
    have hi := (halasz_window_translate_memLp δ β).norm.integrable_sq
    have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      hi (Filter.Eventually.of_forall (fun α => by
        simpa only [ite_eq_left hn] using halasz_window_product_bound δ α β γ))
    apply hh.trans_eq
    have : (halaszVinogradovHaar k).IsAddRightInvariant := by
      unfold halaszVinogradovHaar
      infer_instance
    rw [integral_add_right_eq_self (fun α => ‖halaszTorusWindow δ α‖^2) β,
      halasz_torus_window_square_integral δ hδ hδhalf]
  · rw [ite_eq_right hn]
    have hz : ∀ α, ‖conj (halaszTorusWindow δ (α+β))*
        halaszTorusWindow δ (α+γ)‖=0 := by
      intro α
      have hh := halasz_window_product_bound δ α β γ
      rw [ite_eq_right hn] at hh
      exact le_antisymm hh (norm_nonneg _)
    simp only [hz,integral_zero,le_refl]

noncomputable def halaszWindowL2 {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) : Lp ℂ 2 (halaszVinogradovHaar k) :=
  (halasz_window_translate_memLp δ β).toLp (fun α => halaszTorusWindow δ (α+β))

lemma halasz_window_l2_coe {k : ℕ} (δ : Fin k → ℝ)
    (β : Fin k → AddCircle (1:ℝ)) :
    (halaszWindowL2 δ β : (Fin k → AddCircle (1:ℝ)) → ℂ) =ᵐ[halaszVinogradovHaar k]
      (fun α => halaszTorusWindow δ (α+β)) :=
  (halasz_window_translate_memLp δ β).coeFn_toLp

lemma halasz_window_l2_overlap {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (β γ : Fin k → AddCircle (1:ℝ)) :
    ‖inner ℂ (halaszWindowL2 δ β) (halaszWindowL2 δ γ)‖≤
      if HalaszWindowNear δ β γ then ∏ j,2*δ j else 0 := by
  rw [L2.inner_def]
  have he : (∫ α,inner ℂ (halaszWindowL2 δ β α) (halaszWindowL2 δ γ α)
      ∂halaszVinogradovHaar k)=
      ∫ α,conj (halaszTorusWindow δ (α+β))*halaszTorusWindow δ (α+γ)
        ∂halaszVinogradovHaar k := by
    apply integral_congr_ae
    filter_upwards [halasz_window_l2_coe δ β,halasz_window_l2_coe δ γ] with α hb hc
    rw [hb,hc]
    simp only [RCLike.inner_apply']
  rw [he]
  exact halasz_window_overlap_integral δ hδ hδhalf β γ

end TwoPointCorrelations

end OAI
