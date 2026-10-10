import OAI.MeasureTheory.Falconer.Recursion.ProfileContactStability
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Uniform contact intervals for almost Frostman regularization profiles -/

namespace Falconer
open Set Filter
open scoped NNReal Topology

def RobustProfileContact (f : ℝ → ℝ) (q t τ γ : ℝ) : Prop :=
  ∃ A B : ℝ, γ ≤ A ∧ A+γ ≤ B ∧ B+γ ≤ 1 ∧ B+γ ≤ 2*A ∧
    (∀ w ∈ Icc 0 A, q*w-τ*(B-A) ≤ f w) ∧
    (∀ w ∈ Icc A B, t*(w-A)-τ*(B-A) ≤ f w-f A) ∧
    (∀ w ∈ Icc B 1, q*(w-B)-τ*(B-A) ≤ f w-f B)

theorem uniform_profile_contact (K : ℝ≥0) {q t s τ : ℝ}
    (hqt : q < t) (hts : t < s) (hτ : 0 < τ) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∀ f : ℝ → ℝ,
      LipschitzOnWith K f (Icc 0 1) → f 0 = 0 →
      (∀ u ∈ Icc (0:ℝ) 1, s*u-ε ≤ f u) → RobustProfileContact f q t τ γ := by
  classical
  by_contra hno
  push Not at hno
  let e : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hc (n : ℕ) : ∃ f : ℝ → ℝ, LipschitzOnWith K f (Icc 0 1) ∧ f 0 = 0 ∧
      (∀ u ∈ Icc (0:ℝ) 1, s*u-e n ≤ f u) ∧ ¬RobustProfileContact f q t τ (e n) :=
    hno (e n) (e n) (hepos n) (hepos n)
  choose f hLip hzero hlower hfail using hc
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨A,B,φ,hA,hAB,hB,hBA,hφ,hcontacts⟩ :=
    profile_sequence_contact f hLip hzero he hlower hqt hts
  have hgap : 0 < τ*(B-A) := mul_pos hτ (sub_pos.mpr hAB)
  obtain ⟨I₀,hI₀⟩ := hcontacts (τ*(B-A)) hgap
  have hem := he.comp hφ.tendsto_atTop
  have heA := hem.eventually (eventually_lt_nhds hA)
  have heAB := hem.eventually (eventually_lt_nhds (sub_pos.mpr hAB))
  have heB := hem.eventually (eventually_lt_nhds (sub_pos.mpr hB))
  have heBA := hem.eventually (eventually_lt_nhds (sub_pos.mpr hBA))
  obtain ⟨i,hi,hiA,hiAB,hiB,hiBA⟩ :=
    ((eventually_ge_atTop I₀).and (heA.and (heAB.and (heB.and heBA)))).exists
  simp only [Function.comp_apply] at hiA hiAB hiB hiBA
  apply hfail (φ i)
  obtain ⟨hfirst,hmiddle,hlast⟩ := hI₀ i hi
  exact ⟨A,B,hiA.le,by linarith,by linarith,by linarith,hfirst,hmiddle,hlast⟩

end Falconer

end OAI
