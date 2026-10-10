import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.OuterPairingLimit
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingRegions

namespace OAI

/-!
# Outer exhaustion and localization of the height pairing

Restricting to expanding outer balls leaves the local bilinear term unchanged
and exhausts the integrable renormalized far term. Equality of the finite-region
pairings then passes to the limit, proving independence of the localization
region for the same supported, mean-zero test function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem restrict_set_inside_ball {d : ℕ} (μ : Measure (Ambient d))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (a : Ambient d) (T : ℝ)
    (hsub : s ⊆ ball a T) : (μ.restrict (ball a T)).restrict s = μ.restrict s := by
  rw [Measure.restrict_restrict hs, inter_eq_left.mpr hsub]

theorem heightPairingOn_restrict_outer_ball {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (T : ℝ) (hsub : s ⊆ ball a T)
    (w φ : Ambient d → ℝ) :
    heightPairingOn m (μ.restrict (ball a T)) a s w φ =
      (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
        ∂(μ.restrict s).prod (μ.restrict s)) +
      ∫ q in univ ×ˢ ball a T, renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
  have hcomm : (μ.restrict (ball a T)).restrict sᶜ = (μ.restrict sᶜ).restrict (ball a T) := by
    rw [Measure.restrict_restrict hs.compl, Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict s).prod ((μ.restrict sᶜ).restrict (ball a T)) =
      ((μ.restrict s).prod (μ.restrict sᶜ)).restrict (univ ×ˢ ball a T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold heightPairingOn
  rw [restrict_set_inside_ball μ s hs a T hsub, hcomm, hprod]

theorem heightPairingOn_outer_limit {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (T₀ : ℝ) (hsub : s ⊆ ball a T₀)
    (w φ : Ambient d → ℝ)
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ))) :
    Tendsto (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ)
      atTop (𝓝 (heightPairingOn m μ a s w φ)) := by
  have ht := integral_outer_pair_exhaustion ((μ.restrict s).prod (μ.restrict sᶜ)) a T₀
    (renormalizedNormalIntegrand m w φ a) hfar
  have heq : (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ) =
      fun k => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2
        ∂(μ.restrict s).prod (μ.restrict s)) +
      ∫ q in univ ×ˢ ball a (outerPairRadius T₀ k), renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict s).prod (μ.restrict sᶜ) := by
    funext k
    exact heightPairingOn_restrict_outer_ball m μ a s hs _
      (hsub.trans (ball_subset_ball (outerPairRadius_ge T₀ k))) w φ
  rw [heq]
  exact tendsto_const_nhds.add ht

theorem center_height_integrable_finite_region {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (w : Ambient d → ℝ) (hw : Integrable w ν)
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hcontain : ball a r ⊆ s) :
    IntegrableOn (fun y => w y * inverseDistancePow (m + 1) a y) sᶜ ν := by
  apply hw.restrict.mul_bdd (inverseDistancePow_measurable (m + 1) a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs.compl] with y hy
  have hd : r ≤ dist a y := by
    by_contra h
    exact hy (hcontain (by simpa only [mem_ball, dist_comm] using! (lt_of_not_ge h)))
  rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
  simpa only [inverseDistancePow, one_div] using!
    one_div_le_one_div_of_le (pow_pos hr (m + 1)) (pow_le_pow_left₀ hr.le hd (m + 1))

theorem heightPairingOn_localization_independent {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ] (a : Ambient d)
    (s t : Set (Ambient d)) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (r T₀ : ℝ) (hr : 0 < r) (hins : ball a r ⊆ s) (hint : ball a r ⊆ t)
    (hsout : s ⊆ ball a T₀) (htout : t ⊆ ball a T₀)
    (w φ : Ambient d → ℝ) (hφ : Integrable φ μ)
    (hφs : ∀ x ∉ s, φ x = 0) (hφt : ∀ x ∉ t, φ x = 0) (hzero : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ k, Integrable w (μ.restrict (ball a (outerPairRadius T₀ k))))
    (hF : ∀ k, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (ball a (outerPairRadius T₀ k))).prod
        (μ.restrict (ball a (outerPairRadius T₀ k)))))
    (hfarS : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict s).prod (μ.restrict sᶜ)))
    (hfarT : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict t).prod (μ.restrict tᶜ))) :
    heightPairingOn m μ a s w φ = heightPairingOn m μ a t w φ := by
  have hlimS := heightPairingOn_outer_limit m μ a s hs T₀ hsout w φ hfarS
  have hlimT := heightPairingOn_outer_limit m μ a t ht T₀ htout w φ hfarT
  have heq : (fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a s w φ) =
      fun k => heightPairingOn m (μ.restrict (ball a (outerPairRadius T₀ k))) a t w φ := by
    funext k
    let T := outerPairRadius T₀ k
    let ν := μ.restrict (ball a T)
    let : IsFiniteMeasure ν := ⟨by
      simpa only [ν, Measure.restrict_apply_univ] using!
        (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a T).measure_lt_top⟩
    have hsubS : s ⊆ ball a T := hsout.trans (ball_subset_ball (outerPairRadius_ge T₀ k))
    have hsubT : t ⊆ ball a T := htout.trans (ball_subset_ball (outerPairRadius_ge T₀ k))
    have hzS : (∫ x in s, φ x ∂ν) = 0 := by
      rw [show ν.restrict s = μ.restrict s from restrict_set_inside_ball μ s hs a T hsubS]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφs).trans hzero
    have hzT : (∫ x in t, φ x ∂ν) = 0 := by
      rw [show ν.restrict t = μ.restrict t from restrict_set_inside_ball μ t ht a T hsubT]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφt).trans hzero
    have hS := (finite_height_pairing_eq_renormalized m w φ ν a s hs hφ.restrict hφs hzS
      (center_height_integrable_finite_region m ν w (hw k) a r hr s hs hins) (hF k)).2
    have hT := (finite_height_pairing_eq_renormalized m w φ ν a t ht hφ.restrict hφt hzT
      (center_height_integrable_finite_region m ν w (hw k) a r hr t ht hint) (hF k)).2
    exact hS.symm.trans hT
  rw [heq] at hlimS
  exact tendsto_nhds_unique hlimS hlimT

end

end RieszRectifiability

end OAI
