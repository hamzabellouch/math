import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCascadeBlock
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianKernel

namespace OAI

/-! Finite cascade averaging for bounded measurable tests. This includes
the hard spatial restrictions used before normalizer regularization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_finite_block_measurable_average {m n r : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (H : SpectralBlock m r → ℝ) (hH : Measurable H) {M : ℝ}
    (hbound : ∀ x, ‖H x‖ ≤ M) :
    (∫ x, H (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
        (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n,
        H (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ)
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  have hm : Measurable (fun x : JointArray => H
      (cavitySynchronizedBlock (cavityCanonicalDiagonal ρ eig hρ hsum p)
        (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x))) :=
    hH.comp ((continuous_cavitySynchronizedBlock _ _
      (continuous_cavityCanonicalLabel ρ eig hρ hsum p)).measurable.comp
      (by unfold arrayBlock spinArray; fun_prop))
  rw [cascadeCompact_integral n b _ hm]
  simp_rw [cavity_finite_compact_block ρ eig hρ hsum p q hq hq0 hq1]
  exact replicaLaw_integral_prefix (labeledCascadeLaw n b : Measure (LabeledTree n))
    (labeledLeafLaw n) (measurable_labeledLeafLaw n) _
    (fun σ => by simpa only [Real.norm_eq_abs] using
      (hbound (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ)))

theorem cavity_finite_gaussian_measurable_average {m n r k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : 0 ≤ q 0) (hq1 : q (Fin.last n) ≤ 1) (b : ℕ → ℝ)
    (F : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin k)) → ℝ)
    (hF : Measurable F) {M : ℝ} (hbound : ∀ x, ‖F x‖ ≤ M) :
    let B := fun x : JointArray => cavitySynchronizedBlock
      (cavityCanonicalDiagonal ρ eig hρ hsum p)
      (cavityCanonicalLabel ρ eig hρ hsum p) (arrayBlock spinArray r x)
    (∫ x, ∫ z, F (B x,z) ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ (B x))
      ∂(cascadeCompactLaw n b (fun i => q (cavityFiniteLevel n i)) : Measure JointArray)) =
      ∫ T, ∫ σ : Fin r → LabeledLeaf n, ∫ z,
        F (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ,z)
        ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ
          (cavityFiniteReplicaSpectralBlock ρ eig hρ hsum p q σ))
        ∂Measure.pi (fun _ => labeledLeafLaw n T)
        ∂(labeledCascadeLaw n b : Measure (LabeledTree n)) := by
  intro B
  let κ := (cavityGaussianKernel (a := Fin m × (Fin r × Fin k))
    (L := SpectralBlock m r)).comap (fun x => (x,cavityGroupBlockCovariance k ρ x))
      (measurable_id.prodMk (continuous_cavityGroupBlockCovariance k ρ).measurable)
  let H : SpectralBlock m r → ℝ := fun x => ∫ z, F (x,z)
    ∂multivariateGaussian 0 (cavityGroupBlockCovariance k ρ x)
  have hH : Measurable H :=
    hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ) |>.measurable
  have hb x : ‖H x‖ ≤ M := by
    have h := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m × (Fin r × Fin k)))
        (cavityGroupBlockCovariance k ρ x)) (ae_of_all _ fun z => hbound (x,z))
    simpa only [H,probReal_univ,mul_one] using h
  exact cavity_finite_block_measurable_average ρ eig hρ hsum p q hq hq0 hq1 b H hH hb

end InvariantIsing

end

end OAI
