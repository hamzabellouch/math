import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.UniformPowerQuotientBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothDamped

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothDampedFamily
open Finset OrdinaryCorrelations SourcePrimeFactor Filter OrdinaryArchimedeanTwist

abbrev PrimeParameters := {i : Parameters // ∀ p ∈ i.1, Nat.Prime p}

theorem uniform_smooth_power_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (P S : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, |t| ≤ (N:ℝ)^k/2 →
        ‖(N:ℂ)⁻¹ * ∑ n ∈ Icc 1 N, twist (smoothDamped f P S z) t n‖ ≤ ε := by
  classical
  rcases Completion.one_or_zero hm with h1 | hz
  · let F : PrimeParameters → ℕ → ℂ := fun i => family f i.1
    have hfF : ∀ i, OneBounded (F i) := fun i =>
      smoothDamped_oneBounded hf i.1.1 i.1.2.1 i.1.2.2.2
    have hmF : ∀ i, Multiplicative (F i) := fun i =>
      smoothDamped_multiplicative hm i.2 i.1.2.1 i.1.2.2
    have h1F : ∀ i, F i 1 = 1 := fun i => smoothDamped_one h1 i.2 i.1.2.1 i.1.2.2
    have hDF : UniformFamilyHalasz.PrincipalDivergence F := by
      intro R
      filter_upwards [family_divergence hf hNP R] with N hN
      intro i t ht
      exact hN i.1 t ht
    filter_upwards [UniformFamilyHalasz.uniform_power_multiplicative_bound hfF hmF h1F hDF k hk hε]
      with N hN
    intro P S hP z hz t ht
    exact hN ⟨(P,S,⟨z,hz⟩),hP⟩ t ht
  · filter_upwards [] with N
    intro P S hP z hz' t ht
    have he : (∑ n ∈ Icc 1 N, twist (smoothDamped f P S z) t n) = 0 := by
      apply sum_eq_zero
      intro n hn
      have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
      simp [twist, smoothDamped, weightedFunction, hz n hn0]
    rw [he, mul_zero, norm_zero]
    exact hε.le

end OrdinarySmoothDampedFamily

end

end OAI
