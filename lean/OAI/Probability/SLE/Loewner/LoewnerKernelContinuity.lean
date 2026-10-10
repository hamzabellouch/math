import OAI.Probability.SLE.Loewner.LoewnerInverseDriverContinuity
import OAI.Probability.SLE.Loewner.UnivalentLocallyUniformLimit

namespace OAI

/-! Compact interior regions of a limiting Loewner domain persist under
uniform perturbations of the driver. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem inverse_image_neighborhood_persists
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (hl : TendstoLocallyUniformlyOn (fun n => F n T) (J T) atTop upperHalfPlane)
    {w : ℂ} (hw : w ∈ upperHalfPlane) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, ball (J T w) r ⊆ survivingDomain (γ n) T := by
  let R := w.im/2
  have hwpos : 0 < w.im := hw
  have hR : 0 < R := half_pos hw
  have hKH : closedBall w R ⊆ upperHalfPlane := by
    intro z hz
    have hz' : ‖z-w‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hd := (Complex.abs_im_le_norm (z-w)).trans hz'
    simp only [Complex.sub_im] at hd
    change 0 < z.im
    dsimp [R] at hd
    linarith [(abs_le.mp hd).1]
  have hJi : InjOn (J T) upperHalfPlane := by
    intro z hz v hv' he
    rw [← hv.2.2.2.2.2.2.2.2.1 T z hz,he,hv.2.2.2.2.2.2.2.2.1 T v hv']
  have hsep (z : ℂ) (hz : z ∈ sphere w R) : J T z ≠ J T w := by
    intro he
    have heq := hJi (hKH (sphere_subset_closedBall hz)) hw he
    exact (ne_of_mem_sphere hz hR.ne') heq
  have hc : ContinuousOn (fun z => ‖J T z-J T w‖) (sphere w R) :=
    (((hv.2.2.2.2.1 T).continuousOn.mono (sphere_subset_closedBall.trans hKH)).sub
      continuousOn_const).norm
  obtain ⟨v,hvS,hmin⟩ := (isCompact_sphere w R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hc
  let d : ℝ := ‖J T v-J T w‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (hsep v hvS))
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane).mp hl
      (closedBall w R) hKH (isCompact_closedBall _ _))) (d/8) (by positivity)
  refine ⟨d/8,by positivity,?_⟩
  filter_upwards [hsmall] with n hn
  have hn' (z : ℂ) (hz : z ∈ closedBall w R) : ‖F n T z-J T z‖ < d/8 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hn z hz
  have hcenter := hn' w (mem_closedBall_self hR.le)
  have hboundary (z : ℂ) (hz : z ∈ sphere w R) : d/2 ≤ ‖F n T z-F n T w‖ := by
    have herror := hn' z (sphere_subset_closedBall hz)
    have htri : ‖J T z-J T w‖ ≤ ‖J T z-F n T z‖+
        ‖F n T z-F n T w‖+‖F n T w-J T w‖ := by
      calc
        _ = ‖(J T z-F n T z)+(F n T z-F n T w)+(F n T w-J T w)‖ := by congr 1; ring
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [norm_sub_rev (J T z) (F n T z)] at htri
    have hdmin : d ≤ ‖J T z-J T w‖ := hmin hz
    linarith
  have hFi : InjOn (F n T) upperHalfPlane := by
    intro z hz v hv' he
    rw [← (h n).2.2.2.2.2.2.2.2.1 T z hz,he,(h n).2.2.2.2.2.2.2.2.1 T v hv']
  have hdc : DiffContOnCl ℂ (F n T) (ball w R) :=
    ⟨((h n).2.2.2.2.1 T).mono (ball_subset_closedBall.trans hKH),by
      rw [closure_ball w hR.ne']
      exact ((h n).2.2.2.2.1 T).continuousOn.mono hKH⟩
  have hnot : ∃ᶠ z in 𝓝 w, F n T z ≠ F n T w :=
    not_eventually.mp (univalent_not_eventually_constant isOpen_upperHalfPlane hFi hw)
  intro z hz
  have hz' : z ∈ ball (F n T w) ((d/2)/2) := by
    have hdist := dist_triangle z (J T w) (F n T w)
    rw [mem_ball,dist_eq_norm] at hz ⊢
    simp only [dist_eq_norm,norm_sub_rev (J T w) (F n T w)] at hdist
    linarith
  obtain ⟨x,hx,he⟩ := hdc.ball_subset_image_closedBall hR hboundary hnot hz'
  rw [← he]
  exact (h n).2.2.2.2.2.2.1 T (hKH hx)

end SLEExactGauge

end

end OAI
