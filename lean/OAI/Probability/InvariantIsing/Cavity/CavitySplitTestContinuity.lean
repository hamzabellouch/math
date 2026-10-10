import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplitOverlap
import OAI.Probability.InvariantIsing.Cavity.CavityFullSiteIdentity
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Continuous overlap tests are insensitive to removal of finitely many
cavity sites, uniformly over all spin configurations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_split_test_uniform {n : ℕ} (N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ σ τ : Spin (N k+n),
      |Φ (cavityTotalSpinOverlap (σ,τ)) -
        Φ (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n σ).1,
          (cavitySpinSplit (N k) n τ).1))| < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Icc (-1:ℝ) 1) hΦ.continuousOn
  have hi : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNlim)
  have hr : Tendsto (fun k => 2*(n:ℝ)/(N k)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul (2*(n:ℝ))
  intro ε hε
  obtain ⟨δ,hδ,hφ⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  filter_upwards [hr.eventually (Iio_mem_nhds hδ)] with k hk
  intro σ τ
  have hfull := abs_le.mp (abs_cavityTotalSpinOverlap_le (σ,τ))
  have hbase := abs_le.mp (abs_cavityTotalSpinOverlap_le
    ((cavitySpinSplit (N k) n σ).1,(cavitySpinSplit (N k) n τ).1))
  apply (show dist (Φ (cavityTotalSpinOverlap (σ,τ)))
    (Φ (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n σ).1,
      (cavitySpinSplit (N k) n τ).1))) < ε from ?_)
  apply hφ _ hfull _ hbase
  rw [Real.dist_eq]
  apply (cavity_spin_split_overlap_error (hN k) σ τ).trans_lt
  apply lt_of_le_of_lt _ hk
  apply div_le_div_of_nonneg_left (by positivity)
    (Nat.cast_pos.mpr (hN k))
  exact le_add_of_nonneg_right (Nat.cast_nonneg n)

end InvariantIsing

end

end OAI
