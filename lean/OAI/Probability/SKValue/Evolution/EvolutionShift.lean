import Mathlib
import OAI.Probability.SKValue.Evolution.SmoothEvolution

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma deriv_const_add_eq (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y ↦ f (x+y))=fun y ↦ deriv f (x+y) :=
  funext (deriv_comp_const_add f x)

lemma BoundedSmooth.translate {f : ℝ → ℝ} (hf : BoundedSmooth f) (x : ℝ) :
    BoundedSmooth (fun y ↦ f (x+y)) := by
  refine ⟨hf.smooth.comp (contDiff_const.add contDiff_id),?_⟩
  intro n
  obtain ⟨C,hC,hb⟩ := hf.bound n
  refine ⟨C,hC,?_⟩
  simpa only [iteratedDeriv_comp_const_add] using fun y ↦ hb (x+y)

lemma SmoothTerminal.translate {f : ℝ → ℝ} (hf : SmoothTerminal f) (x : ℝ) :
    SmoothTerminal (fun y ↦ f (x+y)) := by
  refine ⟨?_,hf.smooth.comp (contDiff_const.add contDiff_id),?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Real.dist_eq,add_sub_add_left_eq_sub,NNReal.coe_one,one_mul] using hf.lipschitz.dist_le_mul (x+y) (x+z)
  · rw [deriv_const_add_eq]
    exact hf.jets.translate x

lemma SmoothEvolution.space_translate {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (x : ℝ) :
    SmoothEvolution T γ (fun t y ↦ V t (x+y)) := by
  refine ⟨fun t ht ↦ (h.slices t ht).translate x,fun y ↦ h.continuous_value (x+y),?_,?_,?_,?_,?_⟩
  · intro n y
    simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using h.continuous_jet n (x+y)
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,by simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using fun t ht y ↦ hb t ht (x+y)⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.temporal n
    exact ⟨C,hC,by simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using fun s hs t ht y ↦ hb s hs t ht (x+y)⟩
  · intro t ht s hs y
    simpa only [deriv_const_add_eq] using h.value_pde t ht s hs (x+y)
  · intro t ht s hs y
    simpa only [deriv_const_add_eq] using h.gradient_pde t ht s hs (x+y)

lemma SmoothEvolution.time_shift {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    SmoothEvolution (b-a) (fun t ↦ γ (a+t)) (fun t ↦ V (a+t)) := by
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    apply (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) T)).out
      ⟨ha,hab.trans hb⟩ ⟨ha.trans hab,hb⟩
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨fun t ht ↦ h.slices _ (hmem t ht),?_,?_,?_,?_,?_,?_⟩
  · intro x
    exact (h.continuous_value x).comp (continuous_const.add continuous_id).continuousOn hmem
  · intro n x
    exact (h.continuous_jet n x).comp (continuous_const.add continuous_id).continuousOn hmem
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,fun t ht ↦ hb _ (hmem t ht)⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.temporal n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    simpa only [add_sub_add_left_eq_sub] using hb _ (hmem s hs) _ (hmem t ht) x
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2)) a]
    exact h.value_pde _ (hmem t ht) _ (hmem s hs) x
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x)) a]
    exact h.gradient_pde _ (hmem t ht) _ (hmem s hs) x

end SKValue

end

end OAI
