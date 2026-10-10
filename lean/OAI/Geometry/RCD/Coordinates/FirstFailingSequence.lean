import OAI.Geometry.RCD.Coordinates.DyadicRootEventualSplitting
import OAI.Geometry.RCD.Coordinates.FirstFailingRootFrame
import OAI.Geometry.RCD.Metric.CommonMeasuredApproximations
import OAI.Geometry.RCD.Metric.DyadicFlatnessLimit

namespace OAI

/-! # A first failing dyadic scale contradicts the actual root estimates -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.no_first_failing_sequence {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hMeasured : LocalMeasuredCoordinateInput hX) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∀ (p : ℕ → X) (R ε : ℕ → ℝ) (d : ℕ → ℕ),
      (∀ k, 0 < R k) → (∀ k, 2 ≤ d k) → Tendsto d atTop atTop →
      (∀ k, -1 ≤ K*(2*R k)^2) →
      (∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, -δ ≤ K*(R k)^2) →
      (∀ k, a*(3*R k) ≤ 1) → Tendsto ε atTop (𝓝 0) →
      (∀ k, ∀ t : ℝ, 0 < t → t ≤ R k →
        ∃ f : X → Euclidean (m+1), IsPointedApproximation (p k) 0 t 1 (ε k) f) →
      ∀ (u : ℕ → Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
        (v : ℕ → X → Euclidean (m+1)),
      (∀ k, FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) (2*R k) (ε k) (u k) (v k)) →
      (∀ k, ∀ j < d k, ∃ S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1),
        FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) (R k/(2 : ℝ)^j) γ
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) S)
          (fun x => (S : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x)) ∧
        IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
          (ball (p k) (R k/(2 : ℝ)^j)) measurableSet_ball S) →
      (∀ k, ¬∃ S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1),
        FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) (R k/(2 : ℝ)^(d k)) γ
          (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) S)
          (fun x => (S : Euclidean (m+1) →L[ℝ] Euclidean (m+1)).adjoint (v k x)) ∧
        IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
          (ball (p k) (R k/(2 : ℝ)^(d k))) measurableSet_ball S) → False := by
  obtain ⟨γ₀,hγ₀,_,hroot⟩ := hX.first_failing_root_frame hm κ hκ
  refine ⟨γ₀,hγ₀,?_⟩
  intro γ hγ hγle p R ε d hR hd2 hd hK hKsmall hscale hε hflat u v hfirst hbefore hbad
  let r := fun k => R k/(2 : ℝ)^(d k)
  have hr (k : ℕ) : 0 < r k := div_pos (hR k) (by positivity)
  have hrR (k : ℕ) : r k ≤ R k := div_le_self (hR k).le (one_le_pow₀ (by norm_num))
  have hcurv_mono (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
      K*t^2 ≤ K*s^2 ∨ 0 ≤ K*s^2 := by
    by_cases hK0 : 0 ≤ K
    · exact Or.inr (mul_nonneg hK0 (sq_nonneg _))
    · exact Or.inl (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hs hst 2) (le_of_not_ge hK0))
  have hc (k : ℕ) : -1 ≤ K*(r k)^2 := by
    rcases hcurv_mono k (hr k).le (show r k ≤ 2*R k by linarith [hrR k,hR k]) with h | h
    · exact (hK k).trans h
    · linarith
  have hc5 (k : ℕ) : -1 ≤ K*(5*r k)^2 := by
    have hp : (4 : ℝ) ≤ (2 : ℝ)^(d k) := by
      simpa only [show (2 : ℝ)^2=4 by norm_num] using
        pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hd2 k)
    have hrad : 5*r k ≤ 2*R k := by
      have hh : r k*(2 : ℝ)^(d k)=R k := by dsimp only [r]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hp (hr k).le,hr k]
    rcases hcurv_mono k (mul_nonneg (by norm_num) (hr k).le) hrad with h | h
    · exact (hK k).trans h
    · linarith
  have hcs : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, -δ ≤ K*(r k)^2 := by
    intro δ hδ
    filter_upwards [hKsmall δ hδ] with k hk
    rcases hcurv_mono k (hr k).le (hrR k) with h | h
    · exact hk.trans h
    · linarith
  obtain ⟨ε',V,hε',hε'lim,hV⟩ := hMeasured.common_approximations hm p r hr hcs
    (dyadic_flatness_limit p R ε d hR hd hε hflat)
  choose A hAfirst hAn hframes using fun k =>
    hroot γ hγ.le hγle (p k) (R k) (d k) (hR k) (by have := hd2 k; omega)
      (hK k) (u k) (v k) (hbefore k)
  have hRroot (k : ℕ) : (2 : ℝ)^(d k)*r k=R k := by dsimp only [r]; field_simp
  have hscale' (k j : ℕ) (hj : j ≤ d k) : a*(3*((2 : ℝ)^j*r k)) ≤ 1 := by
    have hjR : (2 : ℝ)^j*r k ≤ R k := by
      dsimp only [r]
      rw [dyadic_ancestor_radius (R k) hj]
      exact div_le_self (hR k).le (one_le_pow₀ (by norm_num))
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjR (by norm_num)) ha).trans (hscale k)
  have hΩ (k : ℕ) : ball (p k) ((2 : ℝ)^(d k)*r k) ⊆ ball (p k) (2*R k) := by
    rw [hRroot]
    exact ball_subset_ball (by linarith [hR k])
  have hsplit := dyadic_root_eventual_splitting m hm hX ha hBG hκ.le hκ1 hsmall p r ε' d hr hd
    hc hc5 (fun k => (hε' k).1.le) (fun k => (hε' k).2) hε'lim V hV u v A hAn hscale'
    (fun k j hj => by
      obtain ⟨S,hS,hSn⟩ := hframes k j hj
      exact ⟨S,_,hS,hSn⟩)
    (fun k => (hfirst k).continuous.mono (hΩ k))
    (fun k i => ae_restrict_of_ae_restrict_of_subset (hΩ k) ((hfirst k).representative i))
    (fun k i => ((hfirst k).harmonic i).mono _ _ (hΩ k)) γ hγ
  obtain ⟨k,hk⟩ := hsplit.exists
  exact hbad k ⟨A k,hk,hAn k⟩

end RegularPointCoordinates

end

end OAI
