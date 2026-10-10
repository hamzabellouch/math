import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCascadeBlock
import OAI.Probability.InvariantIsing.Spectral.SpectralDensityContinuity

namespace OAI

/-! Uniform continuity of finite spectral replica blocks in their
scalar overlap levels, including tied levels and the endpoint one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavityCanonicalCoordinate_dist_le {m : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : Fin m) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |cavityCanonicalCoordinate rho lam hrho hsum p a s -
      cavityCanonicalCoordinate rho lam hrho hsum p a t| ≤ |s - t| := by
  simp only [cavityCanonicalCoordinate, Set.projIcc_of_mem zero_le_one hs,
    Set.projIcc_of_mem zero_le_one ht]
  rw [intervalIntegral.integral_interval_sub_left
    (spectralPathDensity_intervalIntegrable rho lam hrho hsum p a hs)
    (spectralPathDensity_intervalIntegrable rho lam hrho hsum p a ht)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := s) (C := 1)
    (f := spectralPathDensity rho lam hrho hsum p a) (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (spectralPathDensity_nonneg rho lam hrho hsum p a r)]
      exact spectralPathDensity_le_one rho lam hrho hsum p a r)
  simpa only [Real.norm_eq_abs, one_mul] using hb

lemma cavity_finite_block_dist_le {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q q' : Fin (n + 1) → ℝ)
    (hq : ∀ i, q i ∈ Icc 0 1) (hq' : ∀ i, q' i ∈ Icc 0 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ i, |q i - q' i| ≤ δ)
    (σ : Fin r → LabeledLeaf n) :
    dist (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q' σ) ≤ δ := by
  apply (dist_pi_le_iff hδ).mpr
  intro i
  apply (dist_pi_le_iff hδ).mpr
  intro j
  apply (dist_pi_le_iff hδ).mpr
  intro a
  by_cases hij : i = j
  · simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, ite_eq_left hij, dist_self]
    exact hδ
  · simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, ite_eq_right hij]
    change |cavityCanonicalCoordinate rho lam hrho hsum p a _ -
      cavityCanonicalCoordinate rho lam hrho hsum p a _| ≤ δ
    exact (cavityCanonicalCoordinate_dist_le rho lam hrho hsum p a (hq _) (hq' _)).trans (hclose _)

lemma cavity_finite_height_test_uniform {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (F : SpectralBlock m r →ᵇ ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ n (q q' : Fin (n + 1) → ℝ),
      (∀ i, q i ∈ Icc 0 1) → (∀ i, q' i ∈ Icc 0 1) →
      (∀ i, |q i - q' i| ≤ δ) → ∀ σ : Fin r → LabeledLeaf n,
      |F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ) -
        F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q' σ)| < ε := by
  intro ε hε
  have hu := (isCompact_univ : IsCompact (univ : Set (SpectralBlock m r))).uniformContinuousOn_of_continuous
    F.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ / 2, half_pos hδ, fun n q q' hq hq' hc σ => ?_⟩
  apply hmod _ (mem_univ _) _ (mem_univ _)
  exact (cavity_finite_block_dist_le rho lam hrho hsum p q q' hq hq'
    (half_pos hδ).le hc σ).trans_lt (half_lt_self hδ)

end InvariantIsing

end

end OAI
