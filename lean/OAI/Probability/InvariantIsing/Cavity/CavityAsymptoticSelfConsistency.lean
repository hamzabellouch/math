import OAI.Probability.InvariantIsing.Cavity.CavitySelfConsistencyLimit

namespace OAI

/-! Asymptotic preservation of plateau values suffices for cavity
self-consistency. Exact ties at every approximation are unnecessary. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_limit_factors_asymptotic_on (p B : OverlapPath) (Bseq : ℕ → ℝ → ℝ)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => Bseq n x - Bseq n y) atTop (𝓝 0))
    (hlim : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))) :
    ∃ g : ℝ → ℝ, Monotone g ∧ (∀ z, 0 ≤ g z ∧ g z ≤ 1) ∧
      B.val =ᵐ[pathMeasure] fun s => g (p s) := by
  let E := D ∩ {s | Tendsto (fun n => Bseq n s) atTop (𝓝 (B s))}
  have hE : ∀ᵐ s ∂pathMeasure, s ∈ E := hDae.and hlim
  have heq : ∀ x, x ∈ E → ∀ y, y ∈ E → p x = p y → B x = B y := by
    intro x hx y hy hxy
    exact sub_eq_zero.mp (tendsto_nhds_unique (hx.2.sub hy.2) (htied x hx.1 y hy.1 hxy))
  exact cavity_limit_factors_through_overlap_on p B (fun _ s => B s) E hE
    (fun _ x hx y hy hxy => heq x hx y hy hxy) (ae_of_all _ fun _ => tendsto_const_nhds)


theorem cavity_self_consistency_asymptotic_l1_on (p : OverlapPath) (B : ℕ → OverlapPath)
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ x, x ∈ D → ∀ y, y ∈ D → p x = p y →
      Tendsto (fun n => B n x - B n y) atTop (𝓝 0))
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
    obtain ⟨g, hg, hgb, hfactor⟩ := cavity_limit_factors_asymptotic_on p Q
      (fun n s => B (φ (ψ n)) s) D hDae (fun x hx y hy hxy => (htied x hx y hy hxy).comp
        (hφ.comp hψ).tendsto_atTop) hpoint
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

end InvariantIsing

end

end OAI
