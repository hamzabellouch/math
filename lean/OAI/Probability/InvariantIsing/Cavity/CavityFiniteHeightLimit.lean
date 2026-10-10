import OAI.Probability.InvariantIsing.Cavity.CavityFiniteHeightContinuity

namespace OAI

/-! Small uniform changes of overlap levels do not change the limiting
spectral-block tests, even when the finite cascade depth grows. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_finite_block_replica_average {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (F : SpectralBlock m r →ᵇ ℝ) :
    (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ σ, F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i))
        ∂replicaLaw (labeledCascadeLaw n b : Measure (LabeledTree n)) (labeledLeafLaw n)
          (measurable_labeledLeafLaw n) := by
  have hm : Measurable (fun x : JointArray => F
      (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))) :=
    F.continuous.measurable.comp
      ((continuous_cavitySynchronizedBlock _ _
        (continuous_cavityCanonicalLabel rho lam hrho hsum p)).measurable.comp
        (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block rho lam hrho hsum p q hq hq0 hq1]
  rfl

theorem cavity_finite_height_integral_error {m r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q q' : (n : ℕ) → Fin (n + 1) → ℝ)
    (hq : ∀ n, Monotone (q n)) (hq' : ∀ n, Monotone (q' n))
    (hqunit : ∀ n i, q n i ∈ Icc 0 1) (hq'unit : ∀ n i, q' n i ∈ Icc 0 1)
    (b : ℕ → ℕ → ℝ) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hclose : ∀ n i, |q n i - q' n i| ≤ η n) (F : SpectralBlock m r →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (b n) (fun i => q n (cavityFiniteLevel n i)) : Measure JointArray)) -
      ∫ x, F (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
          (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
        ∂(cascadeCompactLaw n (b n) (fun i => q' n (cavityFiniteLevel n i)) : Measure JointArray))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := cavity_finite_height_test_uniform rho lam hrho hsum p F
    (ε / 2) (half_pos hε)
  filter_upwards [hη.eventually (Iio_mem_nhds hδ)] with n hn
  rw [Real.dist_eq, sub_zero,
    cavity_finite_block_replica_average rho lam hrho hsum p (q n) (hq n)
      (hqunit n 0).1 (hqunit n (Fin.last n)).2 (b n) F,
    cavity_finite_block_replica_average rho lam hrho hsum p (q' n) (hq' n)
      (hq'unit n 0).1 (hq'unit n (Fin.last n)).2 (b n) F]
  let μ := replicaLaw (labeledCascadeLaw n (b n) : Measure (LabeledTree n)) (labeledLeafLaw n)
    (measurable_labeledLeafLaw n)
  let G := fun σ : ℕ → LabeledLeaf n =>
    F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q n) (fun i => σ i))
  let G' := fun σ : ℕ → LabeledLeaf n =>
    F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q' n) (fun i => σ i))
  have hm (q₀ : Fin (n + 1) → ℝ) : Measurable (fun σ : ℕ → LabeledLeaf n =>
      F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q₀ (fun i => σ i))) := by
    have hprefix : Measurable (fun σ : ℕ → LabeledLeaf n => fun i : Fin r => σ i) := by fun_prop
    exact (measurable_of_countable
      (fun ξ : Fin r → LabeledLeaf n => F (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q₀ ξ))).comp hprefix
  have hi : Integrable G μ := integrable_of_measurable_abs_le (hm (q n))
    (fun σ => by simpa only [Real.norm_eq_abs] using (F.norm_coe_le_norm
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q n) (fun i => σ i))))
  have hi' : Integrable G' μ := integrable_of_measurable_abs_le (hm (q' n))
    (fun σ => by simpa only [Real.norm_eq_abs] using (F.norm_coe_le_norm
      (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p (q' n) (fun i => σ i))))
  change |(∫ σ, G σ ∂μ) - ∫ σ, G' σ ∂μ| < ε
  rw [← integral_sub hi hi']
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun σ => G σ - G' σ)
    (C := ε / 2) (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs]
      exact (hmod n (q n) (q' n) (hqunit n) (hq'unit n)
        (fun i => (hclose n i).trans hn.le) (fun i => σ i)).le)
  have hb' : |∫ σ, G σ - G' σ ∂μ| ≤ ε / 2 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  exact hb'.trans_lt (half_lt_self hε)

end InvariantIsing

end

end OAI
