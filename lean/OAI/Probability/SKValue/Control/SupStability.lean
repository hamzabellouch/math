import Mathlib
import OAI.Probability.SKValue.Control.ControlStability

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def elapsedValue {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (f : Filtration ℝ≥0 m) (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) : ℝ :=
  sSup {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α}

lemma elapsed_values_nonempty {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (f : Filtration ℝ≥0 m) (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) :
    {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α}.Nonempty := by
  exact ⟨_,fun _ _ ↦ 0,fun _ ↦ measurable_const,by norm_num,rfl⟩

lemma elapsed_values_bddAbove {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Filtration ℝ≥0 m)
    {Z : Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    BddAbove {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α} := by
  refine ⟨(∫ ω, ψ (x+Z ω) ∂μ)+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s|),?_⟩
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := elapsedPayoff_difference_bound hZ hψ hψ (fun y ↦ by simp : ∀ y, |ψ y-ψ y|≤(0 : ℝ))
    hα hαb hγ measurable_const hi intervalIntegrable_const hT (x := x) (η := fun _ ↦ 0)
  simp only [elapsedPayoff,controlAccum,zero_mul,intervalIntegral.integral_zero,mul_zero,add_zero,sub_zero,zero_add] at hd
  have hh := (le_abs_self _).trans hd
  change elapsedPayoff μ Z ψ γ T x α≤_
  change elapsedPayoff μ Z ψ γ T x α-(∫ ω, ψ (x+Z ω) ∂μ)≤_ at hh
  linarith

lemma elapsedValue_sub_le {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    elapsedValue μ f Z ψ γ T x≤elapsedValue μ f Z χ η T x+
      (ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|)) := by
  apply csSup_le (elapsed_values_nonempty μ f Z ψ γ T x)
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := (le_abs_self _).trans (elapsedPayoff_difference_bound hZ hψ hχ hε hα hαb hγ hη hiγ hiη hT (x := x))
  have hu : elapsedPayoff μ Z χ η T x α≤elapsedValue μ f Z χ η T x :=
    le_csSup (elapsed_values_bddAbove f hZ hχ hη hiη hT) ⟨α,hα,hαb,rfl⟩
  linarith

lemma elapsedValue_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedValue μ f Z ψ γ T x-elapsedValue μ f Z χ η T x|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  have h1 := elapsedValue_sub_le (f := f) hZ hψ hχ hε hγ hη hiγ hiη hT (x := x)
  have h2 := elapsedValue_sub_le (f := f) hZ hχ hψ (fun y ↦ by rw [abs_sub_comm]; exact hε y) hη hγ hiη hiγ hT (x := x)
  simp_rw [abs_sub_comm (η _) (γ _)] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end SKValue

end

end OAI
