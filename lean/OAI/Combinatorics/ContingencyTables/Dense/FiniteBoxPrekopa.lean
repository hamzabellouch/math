import OAI.Analysis.KLS.Convexity.PrekopaLeindler
import OAI.Combinatorics.ContingencyTables.PublishedInputs
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Discharging the finite-box Prékopa–Leindler input

The finite-function-space Prékopa–Leindler inequality applies to the nonnegative
indicators of the three box unions. Compact-box continuity supplies all
measurability and integrability obligations without assumptions outside
the common box.
-/
namespace ContingencyTables.PublishedInputs
open MeasureTheory Set
open scoped ENNReal
noncomputable section

private theorem integral_interpolation {q : ℕ} {f g h : Point q → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hfg : ∀ x y, f x ^ t * g y ^ (1-t) ≤ h (t • x+(1-t) • y)) :
    (∫ x, f x)^t * (∫ y, g y)^(1-t) ≤ ∫ z, h z := by
  have hp := AsymptoticStatistics.prekopaLeindler hf.ennreal_ofReal hg.ennreal_ofReal
    hh.ennreal_ofReal ht ht1 (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) ht.le,
        ENNReal.ofReal_rpow_of_nonneg (hg0 y) (sub_pos.mpr ht1).le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) t)]
      exact ENNReal.ofReal_le_ofReal (hfg x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0)] at hp
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) ht.le,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) t)] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)).mp hp

theorem IsFiniteBoxUnion.isOpen {q : ℕ} {S : Set (Point q)}
    (hS : IsFiniteBoxUnion S) : IsOpen S := by
  obtain ⟨n,lower,upper,rfl⟩ := hS
  have ho : IsOpen (⋃ k : Fin n, ⋂ i : Fin q,
      {x : Point q | lower k i < x i ∧ x i < upper k i}) :=
    isOpen_iUnion fun k => isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
  convert ho using 1
  ext x
  simp

private theorem box_indicator {q : ℕ} {lower upper : Point q} {S : Set (Point q)}
    {f : Point q → ℝ} (hS : IsFiniteBoxUnion S)
    (hbox : closure S ⊆ Icc lower upper) (hf : ContinuousOn f (Icc lower upper))
    (hp : ∀ x ∈ Icc lower upper, 0 < f x) :
    (∀ x, 0 ≤ S.indicator f x) ∧ Measurable (S.indicator f) ∧
      Integrable (S.indicator f) := by
  classical
  have hs := hS.isOpen.measurableSet
  have hsub : S ⊆ Icc lower upper := subset_closure.trans hbox
  refine ⟨?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx] using (hp x (hsub hx)).le
    · simp only [indicator_of_notMem hx, le_refl]
  · change Measurable (S.piecewise f (fun _ => 0))
    exact (hf.mono hsub).measurable_piecewise continuousOn_const hs
  · exact (hf.integrableOn_Icc.mono_set hsub).integrable_indicator hs

/-- The exact published analytic hypothesis required by both manuscripts. -/
theorem finiteBoxPrekopaLeindler (q : ℕ) : FiniteBoxPrekopaLeindler q := by
  intro t ht ht1 lower upper S₀ S₁ S₂ f₀ f₁ f₂ hS₀ hS₁ hS₂
    hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hp₀ hp₁ hp₂ hcover hle
  obtain ⟨h₀,hm₀,hi₀⟩ := box_indicator hS₀ hb₀ hc₀ hp₀
  obtain ⟨h₁,hm₁,hi₁⟩ := box_indicator hS₁ hb₁ hc₁ hp₁
  obtain ⟨h₂,hm₂,hi₂⟩ := box_indicator hS₂ hb₂ hc₂ hp₂
  have ht' : 0 < 1-t := sub_pos.mpr ht1
  have ht1' : 1-t < 1 := by linarith
  have H := integral_interpolation h₁ h₂ h₀ hm₁ hm₂ hm₀ hi₁ hi₂ hi₀ ht' ht1'
    (fun x y => by
      rw [show 1-(1-t)=t by ring]
      by_cases hx : x ∈ S₁
      · by_cases hy : y ∈ S₂
        · have hz : (1-t) • x+t • y ∈ S₀ := hcover ⟨x,hx,y,hy,rfl⟩
          simpa only [indicator_of_mem hx,indicator_of_mem hy,indicator_of_mem hz]
            using hle x hx y hy
        · rw [indicator_of_notMem hy,Real.zero_rpow (ne_of_gt ht),mul_zero]
          exact h₀ _
      · rw [indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ht'),zero_mul]
        exact h₀ _)
  simpa only [integral_indicator hS₀.isOpen.measurableSet,
    integral_indicator hS₁.isOpen.measurableSet,integral_indicator hS₂.isOpen.measurableSet,
    sub_sub_cancel] using H

end
end ContingencyTables.PublishedInputs

end OAI
