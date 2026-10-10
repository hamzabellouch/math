import OAI.NumberTheory.JointDickman.Amplification.IntegralFromSamples
import OAI.NumberTheory.JointDickman.Analysis.MellinProductSamples

namespace OAI

/-! # Integrating the sparse prime/cofactor product estimate -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

/-- The two sample-cardinality premises concern literal finite subsets of
`E`. The prime and cofactor sampling estimates themselves are proved. -/
theorem ramare_product_sparse_integral (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (E : Set ℝ) (T τ b K : ℝ), MeasurableSet E → 0 ≤ T → 0 ≤ τ →
      E ⊆ Set.Ioc (-T) T → 2*T ≤ a^B →
      let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ))
      (∀ U : Finset ℝ, (∀ t ∈ U, t ∈ E) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
        (U.card:ℝ) ≤ K ∧ ((U.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ) →
      (∀ t ∈ E, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∫ t in E, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
        2*(τ^2*(48000*(2*(1+Real.log (2*T+1))+K*Real.sqrt (2*T)*a/N))+
          b^2*(C/(Real.log a)^2)) := by
  obtain ⟨C,γ,hC,hγ,hsample⟩ := ramare_product_sparse_samples B hB
  refine ⟨C,γ,hC,hγ,?_⟩
  filter_upwards [hsample] with a haSample
  intro N P Q F f ha hx hF hf hQ E T τ b K hEm hT hτ hET hTB Qf hcard hb
  apply bounded_integral_le_twice_samples E hEm _
    (((mrtExponentialPolynomial_continuous _ _ _).mul
      (mrtCofactorPolynomial_continuous P F N a)).norm.pow 2)
    (fun _ _ => sq_nonneg _) hT hET
  intro U hUE hsep
  obtain ⟨hK,hγU⟩ := hcard U hUE hsep
  have hdiam : ∀ x ∈ U, ∀ y ∈ U, |x-y| ≤ 2*T := by
    intro x hx y hy
    obtain ⟨hxlo,hxhi⟩ := hET (hUE x hx)
    obtain ⟨hylo,hyhi⟩ := hET (hUE y hy)
    apply abs_le.mpr
    constructor <;> linarith
  have hh := haSample N P Q F f ha hx hF hf hQ U (2*T) τ b
    (by positivity) hτ hsep hdiam hTB hγU
    (fun t ht hqt => hb t (hUE t ht) hqt)
  apply hh.trans
  gcongr

end JointDickman

end OAI
