import OAI.Probability.InvariantIsing.Cavity.CavityMeasurableTests

namespace OAI

/-! Compactness, tied levels and continuous cavity-spin tests identify
the unique limiting magnetization-overlap path in L1. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_self_consistency_l1_on (p : OverlapPath) (B : ℕ → OverlapPath)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ n x, x ∈ D → ∀ y, y ∈ D → p x = p y → B n x = B n y)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg (fun s => abs_nonneg _))
  · intro ε hε
    by_contra hbad
    have hb : ∃ᶠ n in atTop, ε ≤ ∫ s, |B n s - p s| ∂pathMeasure := by
      simpa only [Filter.not_eventually, not_lt] using hbad
    obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hb
    obtain ⟨Q, ψ, hψ, hpoint, hL1⟩ := overlapPath_ae_l1_subsequence (fun n => B (φ n))
    obtain ⟨g, hg, hgb, hfactor⟩ := cavity_limit_factors_through_overlap_on p Q
      (fun n s => B (φ (ψ n)) s) D hDae (fun n x hx y hy hxy => htied _ x hx y hy hxy) hpoint
    have hQtests (Φ : ℝ →ᵇ ℝ) : (∫ s, Φ (p s) * (Q s - p s) ∂pathMeasure) = 0 := by
      have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
        (F := fun n s => Φ (p s) * (B (φ (ψ n)) s - p s))
        (f := fun s => Φ (p s) * (Q s - p s)) (fun _ => ‖Φ‖)
        (fun n => ((Φ.continuous.measurable.comp p.measurable).mul
          ((B (φ (ψ n))).measurable.sub p.measurable)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_mul]
          have hdiff : |B (φ (ψ n)) s - p s| ≤ 1 := abs_le.mpr
            ⟨by linarith [(B (φ (ψ n))).nonneg s, p.le_one s],
              by linarith [(B (φ (ψ n))).le_one s, p.nonneg s]⟩
          exact (mul_le_mul (Φ.norm_coe_le_norm _) hdiff (abs_nonneg _) (norm_nonneg _)).trans_eq
            (mul_one _)) (by
          filter_upwards [hpoint] with s hs
          exact tendsto_const_nhds.mul (hs.sub_const (p s)))
      exact tendsto_nhds_unique hlim ((htest Φ).comp (hφ.comp hψ).tendsto_atTop)
    have heq := cavity_overlap_self_consistency p Q g hg hgb hfactor hQtests
    have hsame (n : ℕ) : (∫ s, |B (φ (ψ n)) s - Q s| ∂pathMeasure) =
        ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with s hs
      rw [hs]
    have hzero : Tendsto (fun n => ∫ s, |B (φ (ψ n)) s - p s| ∂pathMeasure) atTop (𝓝 0) := by
      simpa only [hsame] using hL1
    obtain ⟨n, hn⟩ := (hzero.eventually (Iio_mem_nhds hε)).exists
    exact (not_le_of_gt hn) (hφbad (ψ n))

theorem cavity_self_consistency_l1 (p : OverlapPath) (B : ℕ → OverlapPath)
    (htied : ∀ n x y, p x = p y → B n x = B n y)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) :=
  cavity_self_consistency_l1_on p B Set.univ (ae_of_all _ fun _ => Set.mem_univ _)
    (fun n x _ y _ => htied n x y) htest

end InvariantIsing

end

end OAI
