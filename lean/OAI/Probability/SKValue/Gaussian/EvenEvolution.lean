import Mathlib
import OAI.Probability.SKValue.Evolution.FiniteStepEvolution

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma gaussian_integral_neg (f : ℝ → ℝ) :
    (∫ z, f (-z) ∂standardGaussian)=∫ z, f z ∂standardGaussian := by
  have he := integral_map_equiv (μ := standardGaussian) (MeasurableEquiv.neg ℝ) f
  have hm : standardGaussian.map (MeasurableEquiv.neg ℝ)=standardGaussian := by
    change (gaussianReal 0 1).map (fun x ↦ -x)=gaussianReal 0 1
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  rw [hm] at he
  exact he.symm

lemma heat_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x) (h x : ℝ) :
    heat h ψ (-x)=heat h ψ x := by
  unfold heat
  rw [←gaussian_integral_neg (fun z ↦ ψ (-x+Real.sqrt h*z))]
  apply integral_congr_ae
  filter_upwards [] with z
  convert! hψ (x+Real.sqrt h*z) using 1
  congr 1
  ring

lemma coleHopf_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x) (c h x : ℝ) :
    coleHopf c h ψ (-x)=coleHopf c h ψ x := by
  unfold coleHopf
  split_ifs
  · exact heat_even hψ h x
  · rw [heat_even (fun x ↦ by rw [hψ x])]

lemma profileValue_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x)
    (l : HeatProfile) (t x : ℝ) : profileValue ψ l t (-x)=profileValue ψ l t x := by
  induction l generalizing t x with
  | nil => exact hψ x
  | cons p l ih =>
    change (patchTime (E := ℝ → ℝ) _ _ _ t) (-x)=(patchTime (E := ℝ → ℝ) _ _ _ t) x
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact coleHopf_even (fun y ↦ ih 0 y) _ _ _
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ _

lemma deriv_even_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x)=f x) : deriv f 0=0 := by
  have he : (fun x ↦ f (-x))=f := funext hf
  have hd := deriv_comp_neg f (0 : ℝ)
  rw [he,neg_zero] at hd
  linarith

lemma SmoothTerminal.profile_gradient_strip {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (heven : ∀ x, ψ (-x)=ψ x) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    ∃ K L, GradientStrip (profileTime l) (profileCoeff l)
      (fun t ↦ deriv (profileValue ψ l t)) K L := by
  apply (hψ.profile_evolution l).toGradientStrip (profileTime_nonneg l)
    (fun t _ ↦ profileCoeff_nonneg l t) (profileCoeff_mono hl)
  exact deriv_even_zero (profileValue_even heven l 0)

end SKValue

end

end OAI
