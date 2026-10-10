import OAI.NumberTheory.JointDickman.Probability.GrowingMomentParameters

namespace OAI

/-! # Uniform sparse samples of a prime block with growing endpoints -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma prime_block_reciprocal_mass (M : ℕ) (hM : 0 < M) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (M:ℝ)/3 ≤ (p:ℝ) ∧ p ≤ M)
    (f : ℕ → ℂ) (hf : OneBounded f) :
    (∑ p ∈ P, ‖f p/(p:ℂ)‖^2) ≤ 9/(M:ℝ) := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hcard : (P.card:ℝ) ≤ M := by
    have hs : P ⊆ Icc 1 M := fun p hp => mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2.2⟩
    have hh := card_le_card hs
    simpa using (show (P.card:ℝ) ≤ ((Icc 1 M).card:ℝ) by exact_mod_cast hh)
  calc
    _ ≤ ∑ _p ∈ P, (3/(M:ℝ))^2 := by
      apply sum_le_sum
      intro p hp
      have hpr : 0 < (p:ℝ) := by exact_mod_cast (hP p hp).1.pos
      rw [norm_div,Complex.norm_natCast]
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_div_of_nonneg_right (hf p (hP p hp).1.pos) hpr.le).trans
      apply (div_le_div_iff₀ hpr hMr).mpr
      linarith [(hP p hp).2.1]
    _ = (P.card:ℝ)*(3/(M:ℝ))^2 := by simp
    _ ≤ (M:ℝ)*(3/(M:ℝ))^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 9/(M:ℝ) := by field_simp; norm_num

/-- At threshold `M^(-1/6)`, a block whose endpoints grow faster than a
large logarithmic power has fewer than `X^(5/12)` separated large values. -/
theorem growing_prime_samples : ∀ᶠ X : ℝ in atTop,
    ∀ M : ℕ, 2 ≤ M → 1 ≤ Real.log (M:ℝ) →
      (Real.log X)^100 ≤ (M:ℝ) → (M:ℝ) ≤ X^(1/100:ℝ) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (M:ℝ)/3 ≤ (p:ℝ) ∧ p ≤ M) →
      ∀ f : ℕ → ℂ, OneBounded f → ∀ V : ℝ, 0 < V → (M:ℝ)^(-1/6:ℝ) ≤ V →
      ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ X) →
      (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ U, V ≤ ‖mrtExponentialPolynomial P (fun p => f p/(p:ℂ))
        (fun p => -Real.log (p:ℝ)) t‖) → (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  filter_upwards [subsquare_prime_samples,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 3),eventually_ge_atTop 1]
    with X hX hlogX hX1
  intro M hM hlogM hlarge hscale P hP f hf V hV hMV U hU hsep hlargeU
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
  obtain ⟨hlo,hhi,hr⟩ := growingPrimeMoment_bounds hX1 hlogM hM0
  apply hX M (growingPrimeMoment X M) hM hlo hhi hscale P
    (fun p => f p/(p:ℂ)) (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2.2)
    X V (by linarith) le_rfl hV _ U hU hsep hlargeU
  exact growing_moment_mass hlogX hM0 hlarge hr hMV
    (prime_block_reciprocal_mass M (by omega) P hP f hf)

end JointDickman

end OAI
