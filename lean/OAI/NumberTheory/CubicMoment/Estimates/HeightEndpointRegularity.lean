import OAI.NumberTheory.CubicMoment.Estimates.SharpHeightMultiplier
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearValue

namespace OAI

/-! Smoothness at the removable reciprocal singularity, compact support,
and the exact two-endpoint formula for a localized cutoff. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma abs_lt_not_mem_dyadic {T t : ℝ} (ht : |t| < T) :
    t ∉ dyadicHeightSupport T := by
  rintro (hp | hn)
  · exact (not_le_of_gt ht) (hp.1.trans (le_abs_self t))
  · exact (not_le_of_gt ht) ((by linarith [hn.2] : T ≤ -t).trans (neg_le_abs t))

lemma localizedEndpointWeight_smooth (S : ℝ) {T : ℝ} (hT : 0 < T) :
    ContDiff ℝ ∞ (localizedEndpointWeight S T) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : ∀ᶠ t : ℝ in 𝓝 0, |t| < T :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hT)
    filter_upwards [hn] with t ht
    exact localizedEndpointWeight_zero S hT t (abs_lt_not_mem_dyadic ht)
  · unfold localizedEndpointWeight
    apply ContDiffAt.mul _ (heightWindow_smooth T).contDiffAt
    simp only [div_eq_mul_inv]
    apply ContDiffAt.mul
    · exact (contDiff_const.mul (frequencyCutoff.smooth'.comp
        ((contDiff_id.div_const (2*Real.pi)).div_const S))).contDiffAt
    · exact (Complex.ofRealCLM.contDiff.mul contDiff_const).contDiffAt.inv
        (mul_ne_zero (by change (x:ℂ) ≠ 0; exact_mod_cast hx) Complex.I_ne_zero)

lemma localizedEndpointWeight_tsupport (S : ℝ) {T : ℝ} (hT : 0 < T) :
    tsupport (localizedEndpointWeight S T) ⊆ dyadicHeightSupport T := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hh
  exact ht (localizedEndpointWeight_zero S hT t hh)

lemma localizedEndpointWeight_compact (S : ℝ) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (localizedEndpointWeight S T) := by
  apply (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure
  exact localizedEndpointWeight_tsupport S hT

lemma localizedEndpointWeight_integrable (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (localizedEndpointWeight S T) :=
  (localizedEndpointWeight_smooth S hT).continuous.integrable_of_hasCompactSupport
    (localizedEndpointWeight_compact S hT)

lemma localizedEndpointWeight_derivatives (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Integrable (deriv (localizedEndpointWeight S T)) ∧
    Differentiable ℝ (deriv (localizedEndpointWeight S T)) ∧
    Integrable (deriv (deriv (localizedEndpointWeight S T))) := by
  have hd := (contDiff_infty_iff_deriv.mp (localizedEndpointWeight_smooth S hT)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := (localizedEndpointWeight_compact S hT).deriv
  exact ⟨hd.continuous.integrable_of_hasCompactSupport hc,
    hd.differentiable (by simp), hdd.continuous.integrable_of_hasCompactSupport hc.deriv⟩

lemma localizedEndpointWeight_second_zero (S : ℝ) {T : ℝ} (hT : 0 < T) (t : ℝ)
    (ht : t ∉ dyadicHeightSupport T) :
    deriv (deriv (localizedEndpointWeight S T)) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hh
  exact ht (localizedEndpointWeight_tsupport S hT (tsupport_deriv_subset hh))

lemma cutoff_window_fourier_endpoints (S : ℝ) {T : ℝ} (hT : 0 < T) (ℓ : ℝ) :
    heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t) ℓ =
      (T:ℂ)⁻¹*(heightFourierIntegral (localizedEndpointWeight S T) ℓ -
        heightFourierIntegral (localizedEndpointWeight S T) (ℓ-Real.log 2)) := by
  have hi := localizedEndpointWeight_integrable S hT
  simp only [heightFourierIntegral_eq]
  rw [← integral_sub (integrable_height_phase _ hi ℓ)
    (integrable_height_phase _ hi (ℓ-Real.log 2)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [cutoffHeightMultiplier_window_endpoints S hT t]
  have he : Complex.exp (((ℓ-Real.log 2)*t:ℝ)*Complex.I) =
      Complex.exp ((ℓ*t:ℝ)*Complex.I)*Complex.exp ((-Real.log 2*t:ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem bilinear_cutoff_window_endpoints (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (S : ℝ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier S t*heightWindow T t)
        (Real.log (norm (a*b))-Real.log X)) =
      heightBilinearValue P B α β (localizedEndpointWeight S T) X T -
        heightBilinearValue P B α β (localizedEndpointWeight S T) (2*X) T := by
  simp only [heightBilinearValue, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [cutoff_window_fourier_endpoints S hT,
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']
  have he : Real.log (norm (a*b))-Real.log X-Real.log 2 =
      Real.log (norm (a*b))-(Real.log 2+Real.log X) := by ring
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
