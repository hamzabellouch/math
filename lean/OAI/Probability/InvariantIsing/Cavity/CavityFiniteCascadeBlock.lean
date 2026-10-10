import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGroupSelection

namespace OAI

/-! A finite spectral cascade block is the pushforward of the actual
labeled-tree replica law. This identifies bounded block averages without
adding a limiting-law assumption. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_finite_compact_block {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (σ : ℕ → LabeledLeaf n) :
    cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
      (cavityCanonicalLabel rho lam hrho hsum p)
      (arrayBlock spinArray r (compactScalarArray (diagonalPatch 1
        (cascadeScalarArray n (fun i => q (cavityFiniteLevel n i)) σ)))) =
      cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q (fun i => σ i) := by
  have ha : Monotone (fun i => q (cavityFiniteLevel n i)) :=
    hq.comp (cavityFiniteLevel_monotone n)
  have ha0 : 0 ≤ q (cavityFiniteLevel n 0) := by simpa [cavityFiniteLevel] using hq0
  have ha1 : q (cavityFiniteLevel n n) ≤ 1 := by
    simpa only [cavityFiniteLevel_last] using hq1
  ext i j a
  simp only [cavityFiniteReplicaSpectralBlock, cavitySynchronizedBlock, arrayBlock,
    cascadeCompact_spin n ha ha0 ha1 σ, diagonalPatch, cascadeScalarArray, Fin.val_inj]
  split_ifs <;> rfl

theorem cavity_finite_cascade_block_average {m n r : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (H : SpectralBlock m r →ᵇ ℝ) :
    (∫ x, H (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n,
        H (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hm : Measurable (fun x : JointArray => H
      (cavitySynchronizedBlock (cavityCanonicalDiagonal rho lam hrho hsum p)
        (cavityCanonicalLabel rho lam hrho hsum p) (arrayBlock spinArray r x))) :=
    H.continuous.measurable.comp
    ((continuous_cavitySynchronizedBlock _ _
      (continuous_cavityCanonicalLabel rho lam hrho hsum p)).measurable.comp
      (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block rho lam hrho hsum p q hq hq0 hq1]
  exact replicaLaw_integral_prefix (labeledCascadeLaw n b : Measure (LabeledTree n))
    (labeledLeafLaw n) (measurable_labeledLeafLaw n)
    (fun σ => H (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ))
    (fun σ => by simpa only [Real.norm_eq_abs] using
      (H.norm_coe_le_norm (cavityFiniteReplicaSpectralBlock rho lam hrho hsum p q σ)))

end InvariantIsing

end

end OAI
