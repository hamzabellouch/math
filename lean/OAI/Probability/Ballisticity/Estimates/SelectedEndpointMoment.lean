import Mathlib
import OAI.Probability.Ballisticity.Estimates.CurveEndpointLaw

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def selectedEndpointLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N E : Set Ω) (Y : Ω → ℝ) (b : ℝ) (failure strict : Prop)
    [Decidable failure] [Decidable strict] : Measure ℝ :=
  if failure then Measure.dirac b else (μ[|if strict then E else N]).map Y

lemma capped_selection_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W Y : Ω → ℝ)
    (hW : Measurable W) (hY : Measurable Y) {b A B : ℝ}
    (hA : 0 ≤ A) (hAB : A < B) (hW0 : ∀ x, 0 ≤ W x)
    (hYW : ∀ x, |Y x-b| ≤ W x) (hN : μ {x | W x ≤ B} ≠ 0) :
    (∫ x, (Y x-b)^2 ∂μ[|{x | W x ≤ B}]) ≤ A^2+
      2*∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ := by
  let N := {x | W x ≤ B}
  let F := fun x => (Y x-b)^2
  let G := fun x => if A < W x then (min (W x) B)^2 else 0
  have hB : 0 ≤ B := hA.trans hAB.le
  apply conditional_selection_moment μ N (measurableSet_le hW measurable_const) hN F G
    (by fun_prop) (by exact Measurable.ite (measurableSet_lt measurable_const hW) (by fun_prop) measurable_const)
    (sq_nonneg A) (sq_nonneg B)
  · intro x; exact sq_nonneg _
  · intro x hx
    have hh := (hYW x).trans hx
    nlinarith [sq_abs (Y x-b),sq_nonneg (B-|Y x-b|),abs_nonneg (Y x-b)]
  · intro x; dsimp [G]; split_ifs <;> positivity
  · intro x
    dsimp [G]
    split_ifs
    · have hm0 : 0 ≤ min (W x) B := le_min (hW0 x) hB
      have hmB : min (W x) B ≤ B := min_le_right _ _
      nlinarith
    · positivity
  · intro x hx
    have hx' : B < W x := lt_of_not_ge hx
    simp [G,hAB.trans hx',min_eq_right hx'.le]
  · intro x hx
    dsimp [F,G]
    by_cases hax : A < W x
    · rw [ite_eq_left hax,min_eq_left hx]
      have hh := hYW x
      nlinarith [sq_abs (Y x-b),sq_nonneg (W x-|Y x-b|),abs_nonneg (Y x-b),sq_nonneg A]
    · rw [ite_eq_right hax]
      have hh := (hYW x).trans (le_of_not_gt hax)
      nlinarith [sq_abs (Y x-b),sq_nonneg (A-|Y x-b|),abs_nonneg (Y x-b)]

lemma conditional_bounded_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (hμE : μ E ≠ 0)
    (hμEtop : μ E ≠ ∞) (Y : Ω → ℝ) (hY : Measurable Y) {b ρ : ℝ}
    (hρ : 0 ≤ ρ) (hbound : ∀ x ∈ E, |Y x-b| ≤ ρ) :
    (∫ x, (Y x-b)^2 ∂μ[|E]) ≤ ρ^2 := by
  let : IsProbabilityMeasure μ[|E] := ⟨by simp [ProbabilityTheory.cond,Measure.smul_apply,
    ENNReal.inv_mul_cancel hμE hμEtop]⟩
  have hb : ∀ᵐ x ∂μ[|E], (Y x-b)^2 ≤ ρ^2 := by
    filter_upwards [ae_cond_mem hE] with x hx
    have hh := hbound x hx
    nlinarith [sq_abs (Y x-b),sq_nonneg (ρ-|Y x-b|),abs_nonneg (Y x-b)]
  have hi : Integrable (fun x => (Y x-b)^2) μ[|E] :=
    Integrable.of_bound (by fun_prop) (ρ^2) (hb.mono fun x hx => by simpa using hx)
  simpa using integral_mono_ae hi (integrable_const (ρ^2)) hb

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma selectedEndpointLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N E : Set Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (b : ℝ) (failure strict : Prop) [Decidable failure] [Decidable strict]
    (hN : μ N ≠ 0) (hNt : μ N ≠ ∞) (hE : strict → μ E ≠ 0)
    (hEt : μ E ≠ ∞) : IsProbabilityMeasure (selectedEndpointLaw μ N E Y b failure strict) := by
  by_cases hf : failure
  · simp only [selectedEndpointLaw,ite_eq_left hf]
    infer_instance
  simp only [selectedEndpointLaw,ite_eq_right hf]
  have hn : μ (if strict then E else N) ≠ 0 := by
    by_cases hs : strict
    · simpa only [ite_eq_left hs] using hE hs
    · simpa only [ite_eq_right hs] using hN
  have ht : μ (if strict then E else N) ≠ ∞ := by
    by_cases hs : strict
    · simpa only [ite_eq_left hs] using hEt
    · simpa only [ite_eq_right hs] using hNt
  let : IsProbabilityMeasure μ[|if strict then E else N] := ⟨by
    simpa only [ProbabilityTheory.cond,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
      using ENNReal.inv_mul_cancel hn ht⟩
  exact (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance

lemma selectedEndpointLaw_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W Y : Ω → ℝ)
    (hW : Measurable W) (hY : Measurable Y) (E : Set Ω) (hE : MeasurableSet E)
    {b A B ρ : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hρ : 0 ≤ ρ)
    (hW0 : ∀ x, 0 ≤ W x) (hYW : ∀ x, |Y x-b| ≤ W x)
    (failure strict : Prop) [Decidable failure] [Decidable strict]
    (hN : μ {x | W x ≤ B} ≠ 0) (hμE : strict → μ E ≠ 0)
    (hbound : ∀ x ∈ E, |Y x-b| ≤ ρ) :
    (∫ u, (u-b)^2 ∂selectedEndpointLaw μ {x | W x ≤ B} E Y b failure strict) ≤
      ρ^2+(if strict then 0 else A^2)+
        2*(∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ) := by
  have htail : 0 ≤ ∫ x, if A < W x then (min (W x) B)^2 else 0 ∂μ :=
    integral_nonneg fun x => by split_ifs <;> positivity
  by_cases hf : failure
  · simp only [selectedEndpointLaw,ite_eq_left hf,integral_dirac,sub_self,zero_pow (by decide : 2 ≠ 0)]
    split_ifs <;> positivity
  simp only [selectedEndpointLaw,ite_eq_right hf]
  by_cases hs : strict
  · simp only [ite_eq_left hs]
    rw [integral_map hY.aemeasurable (by fun_prop)]
    have hh := conditional_bounded_square μ E hE (hμE hs) (measure_ne_top _ _) Y hY hρ hbound
    linarith
  · simp only [ite_eq_right hs]
    rw [integral_map hY.aemeasurable (by fun_prop)]
    have hh := capped_selection_moment μ W Y hW hY hA hAB hW0 hYW hN
    nlinarith [sq_nonneg ρ]

end DirectionalTransience

end

end

end OAI
