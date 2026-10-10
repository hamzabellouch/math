import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.CompactIntegral
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory

theorem hasDerivAt_integral {n : ℕ} {F : ℝ × Coord n → ℝ}
    (hF : ContDiff ℝ 1 F) (t : ℝ) {K : Set (Coord n)} (hK : IsCompact K)
    (hoff : ∀ s ∈ Icc (t - 1) (t + 1), ∀ X ∉ K, F (s, X) = 0) :
    HasDerivAt (fun s => ∫ X, F (s, X))
      (∫ X, fderiv ℝ F (t, X) (1, 0)) t := by
  let F' : ℝ → Coord n → ℝ := fun s X => fderiv ℝ F (s, X) (1, 0)
  have hd (s : ℝ) (X : Coord n) : HasDerivAt (fun r => F (r, X)) (F' s X) s := by
    have hpair : HasDerivAt (fun r : ℝ => (r, X)) (1, 0) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s X)
    exact ((hF.differentiable (by norm_num) (s, X)).hasFDerivAt.comp_hasDerivAt s hpair)
  have hFc : Continuous F := hF.continuous
  have hF'c : Continuous (fun q : ℝ × Coord n => F' q.1 q.2) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hF'supp {s : ℝ} (hs : s ∈ Ioo (t - 1) (t + 1)) {X : Coord n} (hX : X ∉ K) :
      F' s X = 0 := by
    have he : (fun r => F (r, X)) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact hoff r hr X hX
    exact (hd s X).unique ((hasDerivAt_const s 0).congr_of_eventuallyEq he)
  have hFcpt : HasCompactSupport (fun X => F (t, X)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro X hX
    by_contra hnot
    exact hX (hoff t (by constructor <;> linarith) X hnot)
  have hFcX (s : ℝ) : Continuous (fun X => F (s, X)) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hF'cX : Continuous (F' t) := hF'c.comp (continuous_const.prodMk continuous_id)
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := t - 1) (b := t + 1)).prod hK).exists_bound_of_continuousOn hF'c.continuousOn
  let bound : Coord n → ℝ := K.indicator (fun _ => B)
  have hboundint : Integrable bound := by
    exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const (C := B) (hK.measure_lt_top (μ := volume)).ne)
  have hb : ∀ X, ∀ s ∈ Ioo (t - 1) (t + 1), ‖F' s X‖ ≤ bound X := by
    intro X s hs
    by_cases hX : X ∈ K
    · simpa only [bound, indicator_of_mem hX] using hB (s, X) ⟨⟨hs.1.le, hs.2.le⟩, hX⟩
    · simp only [hF'supp hs hX, norm_zero, bound, indicator_of_notMem hX, le_refl]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => (hFcX s).aestronglyMeasurable))
    ((hFcX t).integrable_of_hasCompactSupport hFcpt) hF'cX.aestronglyMeasurable
    (Filter.Eventually.of_forall hb) hboundint
    (Filter.Eventually.of_forall (fun X s _ => hd s X))).2

theorem hasDerivAt_moving_capture {n : ℕ} {φ : Coord n → ℝ}
    {ρ : ℝ → Coord n → ℝ} {c : ℝ → Coord n}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hρ : ContDiff ℝ 1 (uncurry ρ)) (hc : ContDiff ℝ 1 c) (t : ℝ) :
    HasDerivAt (fun s => ∫ X, φ (X - c s) * ρ s X)
      (∫ X, φ (X - c t) * deriv (fun s => ρ s X) t -
        fderiv ℝ φ (X - c t) (deriv c t) * ρ t X) t := by
  let F : ℝ × Coord n → ℝ := fun q => φ (q.2 - c q.1) * ρ q.1 q.2
  have hF : ContDiff ℝ 1 F :=
    (hφ.comp (contDiff_snd.sub (hc.comp contDiff_fst))).mul hρ
  let K : Set (Coord n) := (fun q : ℝ × Coord n => c q.1 + q.2) ''
    (Icc (t - 1) (t + 1) ×ˢ tsupport φ)
  have hK : IsCompact K :=
    (isCompact_Icc.prod hφc).image ((hc.continuous.comp continuous_fst).add continuous_snd)
  have hoff : ∀ s ∈ Icc (t - 1) (t + 1), ∀ X ∉ K, F (s, X) = 0 := by
    intro s hs X hX
    have hz : φ (X - c s) = 0 := by
      by_contra hnz
      apply hX
      refine ⟨(s, X - c s), ⟨hs, subset_closure hnz⟩, ?_⟩
      dsimp only
      abel
    simp only [F, hz, zero_mul]
  have hi := hasDerivAt_integral hF t hK hoff
  have hdF (X : Coord n) : fderiv ℝ F (t, X) (1, 0) =
      φ (X - c t) * deriv (fun s => ρ s X) t -
        fderiv ℝ φ (X - c t) (deriv c t) * ρ t X := by
    have hdiff : HasFDerivAt F (fderiv ℝ F (t, X)) (t, X) :=
      (hF.differentiable (by norm_num) (t, X)).hasFDerivAt
    have hline : HasDerivAt (fun s => F (s, X)) (fderiv ℝ F (t, X) (1, 0)) t := by
      simpa only [Function.comp_def, id_eq] using
        hdiff.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t X))
    have hρX : ContDiff ℝ 1 (fun s => ρ s X) := hρ.comp (contDiff_id.prodMk contDiff_const)
    have harg := (hasDerivAt_const t X).sub ((hc.differentiable (by norm_num) t).hasDerivAt)
    have hφX := (hφ.differentiable (by norm_num) (X - c t)).hasFDerivAt.comp_hasDerivAt t harg
    have hprod := hφX.mul ((hρX.differentiable (by norm_num) t).hasDerivAt)
    have hval := hline.unique hprod
    simp only [zero_sub, map_neg, Function.comp_apply, Pi.sub_apply] at hval
    rw [hval]
    ring
  have heq : (∫ X, fderiv ℝ F (t, X) (1, 0)) =
      ∫ X, φ (X - c t) * deriv (fun s => ρ s X) t -
        fderiv ℝ φ (X - c t) (deriv c t) * ρ t X :=
    integral_congr_ae (Filter.Eventually.of_forall hdF)
  rw [heq] at hi
  exact hi

end VelocityDetection.CompactIntegral
end

end OAI
