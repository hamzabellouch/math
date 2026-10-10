import OAI.NumberTheory.JointDickman.Analysis.MellinRealScale
import OAI.NumberTheory.JointDickman.Counting.SparseCofactorSampling
import OAI.NumberTheory.TwoPointCorrelations.MRTPrimeProducts

namespace OAI

/-! # Separating the small and large auxiliary prime values -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

/-- Split the finite product energy at the prime-polynomial threshold.
Only the large-prime class needs the pointwise cofactor bound. -/
lemma mellin_product_sample_split (S : Finset ℝ) (Q R : ℝ → ℂ)
    {τ b : ℝ} (_hτ : 0 ≤ τ)
    (hR : ∀ t ∈ S, τ < ‖Q t‖ → ‖R t‖ ≤ b) :
    (∑ t ∈ S, ‖Q t*R t‖^2) ≤
      τ^2*(∑ t ∈ S, ‖R t‖^2)+
        b^2*(∑ t ∈ S.filter (fun t => τ < ‖Q t‖), ‖Q t‖^2) := by
  let E := S.filter (fun t => τ < ‖Q t‖)
  have he : (∑ t ∈ S, ‖Q t*R t‖^2) =
      (∑ t ∈ E, ‖Q t*R t‖^2)+
        (∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖Q t*R t‖^2) := by
    exact (sum_filter_add_sum_filter_not S (fun t => τ < ‖Q t‖) _).symm
  have hlarge : (∑ t ∈ E, ‖Q t*R t‖^2) ≤ b^2*∑ t ∈ E, ‖Q t‖^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [norm_mul, mul_pow, mul_comm (b^2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hR t (mem_filter.mp ht).1 (mem_filter.mp ht).2) 2)
      (sq_nonneg _)
  have hsmall : (∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖Q t*R t‖^2) ≤
      τ^2*∑ t ∈ S, ‖R t‖^2 := by
    apply le_trans (b := τ^2*∑ t ∈ S.filter (fun t => ¬τ < ‖Q t‖), ‖R t‖^2)
    · rw [mul_sum]
      apply sum_le_sum
      intro t ht
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (le_of_not_gt (mem_filter.mp ht).2) 2)
        (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)) (sq_nonneg τ)
  rw [he]
  linarith

/-- Auxiliary-prime sampling in terms of sample counts and cofactor values. -/
theorem ramare_product_sparse_samples (B : ℝ) (hB : 1 ≤ B) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ᶠ a : ℝ in atTop, ∀ (N : ℕ) (P Q : Finset ℕ) (F f : ℕ → ℂ),
      1 ≤ a → 2 ≤ (N:ℝ)/a → OneBounded F → OneBounded f →
      (∀ p ∈ Q, p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*a) →
      ∀ (S : Finset ℝ) (T τ b : ℝ), 0 ≤ T → 0 ≤ τ →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) → T ≤ a^B →
      let Qf := mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ))
      ((S.filter (fun t => τ < ‖Qf t‖)).card:ℝ) ≤ a^γ →
      (∀ t ∈ S, τ < ‖Qf t‖ → ‖mrtCofactorPolynomial P F N a t‖ ≤ b) →
      (∑ t ∈ S, ‖Qf t*mrtCofactorPolynomial P F N a t‖^2) ≤
        τ^2*(48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T*a/N))+
          b^2*(C/(Real.log a)^2) := by
  obtain ⟨C,γ,hC,hγ,hprime⟩ := sparse_prime_reciprocal_real B hB
  refine ⟨C,γ,hC,hγ,?_⟩
  filter_upwards [hprime] with a haPrime
  intro N P Q F f ha hx hF hf hQ S T τ b hT hτ hsep hdiam hTB Qf hcard hb
  have hsmall := sparse_ramare_cofactor_sampling P F hF N ha hx S hsep hT hdiam
  have hlarge := haPrime Q (S.filter (fun t => τ < ‖Qf t‖)) hQ
    (fun x hx y hy hxy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
    (fun x hx y hy => (hdiam x (mem_filter.mp hx).1 y (mem_filter.mp hy).1).trans hTB)
    hcard f hf
  apply (mellin_product_sample_split S Qf (mrtCofactorPolynomial P F N a) hτ hb).trans
  exact add_le_add (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _))
    (mul_le_mul_of_nonneg_left hlarge (sq_nonneg _))

end JointDickman

end OAI
