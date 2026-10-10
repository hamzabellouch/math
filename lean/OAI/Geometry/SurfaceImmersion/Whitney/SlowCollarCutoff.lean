import OAI.Geometry.SurfaceImmersion.Atlas.LogarithmicCutoffDerivative

namespace OAI

/-! A smooth cutoff at any prescribed collar radius whose weighted
derivative is arbitrarily small. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem exists_slow_collar_cutoff {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝 (0:ℝ)] (fun _ => 1) ∧ tsupport χ ⊆ Icc (-R) R ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x, |x*deriv χ x| < ε := by
  obtain ⟨C,hC,hb⟩ := smoothTransition_derivative_bound
  let L := (C+1)/ε
  have hL : 0 < L := div_pos (by linarith) hε
  have hCL : C/L < ε := by
    apply (div_lt_iff₀ hL).mpr
    have he : ε*L = C+1 := by dsimp [L]; field_simp
    rw [he]
    linarith
  let χ : ℝ → ℝ := fun x => logarithmicCutoff L (x/R)
  have hχ : ContDiff ℝ ∞ χ := (logarithmicCutoff_smooth hL).comp (contDiff_id.div_const R)
  have hs : tsupport χ ⊆ Icc (-R) R := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hsmall : |x/R| < 1 := lt_of_not_ge (fun h => hx (logarithmicCutoff_zero hL h))
    rw [abs_div,abs_of_pos hR] at hsmall
    exact ⟨(abs_lt.mp ((div_lt_one hR).mp hsmall)).1.le,
      (abs_lt.mp ((div_lt_one hR).mp hsmall)).2.le⟩
  have hc : HasCompactSupport χ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hs
  have hg : χ =ᶠ[𝓝 (0:ℝ)] (fun _ => 1) := by
    have ht : Tendsto (fun x : ℝ => x/R) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq, zero_div] using (continuous_id.div_const R).continuousAt.tendsto (x := (0:ℝ))
    exact (logarithmicCutoff_germ hL).comp_tendsto ht
  refine ⟨χ,hχ,hc,hg,hs,fun x => logarithmicCutoff_range L (x/R),?_⟩
  intro x
  have hd := ((logarithmicCutoff_smooth hL).differentiable (by simp) (x/R)).hasDerivAt.comp x
    ((hasDerivAt_id x).div_const R)
  change HasDerivAt χ _ x at hd
  rw [hd.deriv]
  have he : x*(deriv (logarithmicCutoff L) (x/R)*(1/R)) =
      (x/R)*deriv (logarithmicCutoff L) (x/R) := by ring
  rw [he]
  exact (logarithmicCutoff_weighted_derivative hL hC.le hb (x/R)).trans_lt hCL

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
