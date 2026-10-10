import OAI.Geometry.Perimeter.Regularity.ExistsMinimizingBoundaryAreaGrowth
import OAI.Geometry.Perimeter.Regularity.SmoothFlatOrder

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem tsupport_blowdown_subset_ball {n : ℕ} {φ : Euc n → ℝ} {R : ℝ}
    (hs : tsupport φ ⊆ Metric.ball (0 : Euc n) R) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    tsupport (fun y ↦ φ (r⁻¹ • (y - c))) ⊆ Metric.ball c (r * R) := by
  intro y hy
  have hyb := hs (tsupport_comp_subset_preimage φ
    ((continuous_id.sub continuous_const).const_smul r⁻¹) hy)
  change r⁻¹ • (y - c) ∈ Metric.ball (0 : Euc n) R at hyb
  simp only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hyb
  change dist y c < r * R
  rw [dist_eq_norm]
  have he : r * (r⁻¹ * ‖y - c‖) = ‖y - c‖ := by field_simp
  linarith [mul_lt_mul_of_pos_left hyb hr]

theorem tsupport_directionalDeriv_subset {n : ℕ} (φ : Euc n → ℝ) (w : Euc n) :
    tsupport (fun y ↦ fderiv ℝ φ y w) ⊆ tsupport φ := by
  apply closure_minimal
  · intro y hy
    by_contra hn
    exact hy (by dsimp only; rw [fderiv_of_notMem_tsupport ℝ hn]; rfl)
  · exact isClosed_tsupport φ

theorem setIntegral_eq_of_inter_eq {n : ℕ} {A B U : Set (Euc n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ∩ U = B ∩ U)
    {f : Euc n → ℝ} (hs : tsupport f ⊆ U) :
    (∫ x in A, f x) = ∫ x in B, f x := by
  rw [← integral_indicator hA, ← integral_indicator hB]
  congr 1
  funext x
  by_cases hx : x ∈ U
  · have hm : x ∈ A ↔ x ∈ B := by
      have he := Set.ext_iff.mp hAB x
      simpa only [mem_inter_iff, hx, and_true] using he
    by_cases ha : x ∈ A
    · simp [ha, hm.mp ha]
    · simp [ha, mt hm.mpr ha]
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hx (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb, hz]

theorem polar_blowup_test_error_le {n : ℕ} (hn : 0 < n) {E U : Set (Euc n)}
    (hE : MeasurableSet E) (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {G : Euc n → Euc n} (hG : Integrable G μ)
    (hrep : ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ U → (∫ y in E, divergence V y) = ∫ y, inner ℝ (G y) (V y) ∂μ)
    {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball (0 : Euc n) 2)
    (c v w : Euc n) {r : ℝ} (hr : 0 < r) (hrU : Metric.ball c (r * 2) ⊆ U)
    {M : ℝ} (hM : 0 ≤ M) (hMφ : ∀ y, ‖φ y‖ ≤ M) :
    |(∫ z in blownUpSet E c r, fderiv ℝ φ z w) -
      ((r ^ (n - 1))⁻¹ * ∫ y, φ (r⁻¹ • (y - c)) * inner ℝ v w ∂μ)| ≤
      M * ‖w‖ * ((r ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c (2 * r), ‖G y - v‖ ∂μ) := by
  have hs := tsupport_blowdown_subset_ball hsφ c hr
  rw [integral_fderiv_blownUpSet_polar hE μ G hrep hφ hcφ c w hr (hs.trans hrU)]
  have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  have he : r * (r ^ n)⁻¹ = (r ^ (n - 1))⁻¹ := by
    have hp : r ^ n = r * r ^ (n - 1) := by conv_lhs => rw [hn']; rw [pow_succ']
    rw [hp]; field_simp
  rw [he, ← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
  have hzero : ∀ y ∉ Metric.closedBall c (2 * r), φ (r⁻¹ • (y - c)) = 0 := by
    intro y hy
    have ht : y ∉ tsupport (fun z ↦ φ (r⁻¹ • (z - c))) := fun ht ↦
      hy (Metric.ball_subset_closedBall (by simpa only [mul_comm] using hs ht))
    exact image_eq_zero_of_notMem_tsupport (f := fun z ↦ φ (r⁻¹ • (z - c))) ht
  have hb := polar_test_oscillation_le μ hG v w
    (hφ.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹))
    hM (fun y ↦ hMφ _) (Metric.closedBall c (2 * r)) measurableSet_closedBall hzero
  calc
    _ ≤ (r ^ (n - 1))⁻¹ * (M * ‖w‖ * ∫ y in Metric.closedBall c (2 * r), ‖G y - v‖ ∂μ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem tendsto_doubled_polar_oscillation {n : ℕ} (μ : Measure (Euc n))
    (G : Euc n → Euc n) (c v : Euc n)
    (hlim : Tendsto (fun s : ℝ ↦ (s ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c s,
      ‖G y - v‖ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun i ↦ ((r i) ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c (2 * r i),
      ‖G y - v‖ ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun i ↦ 2 * r i) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [mul_zero] using hr0.const_mul 2,
      Eventually.of_forall (fun i ↦ by change 0 < 2 * r i; exact mul_pos (by norm_num) (hr i))⟩
  have h := (hlim.comp ht).const_mul ((2 : ℝ) ^ (n - 1))
  simp only [mul_zero] at h
  convert h using 1
  funext i
  dsimp only [Function.comp_def]
  rw [mul_pow]
  field_simp [(hr i).ne']

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem flat_distribution_of_polar_blowup_limit {n : ℕ} (hn : 0 < n)
    {E U : Set (Euc n)} (hE : MeasurableSet E)
    (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {G : Euc n → Euc n} (hG : Integrable G μ)
    (hrep : ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ U → (∫ y in E, divergence V y) = ∫ y, inner ℝ (G y) (V y) ∂μ)
    (c v : Euc n)
    (hosc : Tendsto (fun s : ℝ ↦ (s ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c s,
      ‖G y - v‖ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    (hrU : ∀ᶠ i in atTop, Metric.ball c (r i * 2) ⊆ U)
    (A : ℕ → Set (Euc n)) (hA : ∀ i, MeasurableSet (A i))
    (hAE : ∀ i, A i ∩ Metric.ball (0 : Euc n) 2 =
      blownUpSet E c (r i) ∩ Metric.ball (0 : Euc n) 2)
    (F : Set (Euc n)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0)) :
    (∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Euc n) 2 →
      ∀ w, inner ℝ w v = 0 → (∫ x in F, fderiv ℝ φ x w) = 0) ∧
    (∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Euc n) 2 → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x in F, fderiv ℝ φ x v) := by
  let e : ℕ → ℝ := fun i ↦ ((r i) ^ (n - 1))⁻¹ *
    ∫ y in Metric.closedBall c (2 * r i), ‖G y - v‖ ∂μ
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_doubled_polar_oscillation μ G c v hosc hr hr0
  have he0 : ∀ i, 0 ≤ e i := fun i ↦ mul_nonneg
    (inv_nonneg.mpr (pow_nonneg (hr i).le _)) (integral_nonneg fun _ ↦ norm_nonneg _)
  have htest (φ : Euc n → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Metric.ball (0 : Euc n) 2)
      (w : Euc n) :
      Tendsto (fun i ↦ ∫ x in blownUpSet E c (r i), fderiv ℝ φ x w)
        atTop (𝓝 (∫ x in F, fderiv ℝ φ x w)) := by
    have hcD : HasCompactSupport (fun x ↦ fderiv ℝ φ x w) :=
      hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_directionalDeriv_subset φ w)
    have hD : Continuous (fun x ↦ fderiv ℝ φ x w) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have ht := tendsto_setIntegral_of_indicator_L1 A F hA hF hconv
      (hD.integrable_of_hasCompactSupport hcD) (hcD.exists_bound_of_continuous hD)
    convert ht using 1
    funext i
    exact setIntegral_eq_of_inter_eq (measurableSet_blownUpSet hE c (r i)) (hA i)
      (hAE i).symm ((tsupport_directionalDeriv_subset φ w).trans hsφ)
  constructor
  · intro φ hφ hcφ hsφ w hw
    obtain ⟨M, hb⟩ := hcφ.exists_bound_of_continuous hφ.continuous
    have hM : 0 ≤ M := (norm_nonneg (φ 0)).trans (hb 0)
    have hbe : ∀ᶠ i in atTop, |∫ x in blownUpSet E c (r i), fderiv ℝ φ x w| ≤ M * ‖w‖ * e i := by
      filter_upwards [hrU] with i hiU
      have hh := polar_blowup_test_error_le hn hE μ hG hrep hφ hcφ hsφ c v w
        (hr i) hiU hM hb
      have hvw : inner ℝ v w = 0 := by rw [real_inner_comm]; exact hw
      simpa only [hvw, mul_zero, integral_zero, sub_zero] using hh
    have hz : Tendsto (fun i ↦ ∫ x in blownUpSet E c (r i), fderiv ℝ φ x w)
        atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using
        (squeeze_zero' (Eventually.of_forall fun i ↦ abs_nonneg _) hbe
          (by simpa only [mul_zero] using he.const_mul (M * ‖w‖)))
    exact tendsto_nhds_unique (htest φ hφ hcφ hsφ w) hz
  · intro φ hφ hcφ hsφ hφ0
    obtain ⟨M, hb⟩ := hcφ.exists_bound_of_continuous hφ.continuous
    have hM : 0 ≤ M := (norm_nonneg (φ 0)).trans (hb 0)
    have hbtest : ∀ᶠ i in atTop, -(M * ‖v‖ * e i) ≤
        ∫ x in blownUpSet E c (r i), fderiv ℝ φ x v := by
      filter_upwards [hrU] with i hiU
      have hh := polar_blowup_test_error_le hn hE μ hG hrep hφ hcφ hsφ c v v
        (hr i) hiU hM hb
      have hp : 0 ≤ ((r i) ^ (n - 1))⁻¹ *
          ∫ y, φ ((r i)⁻¹ • (y - c)) * inner ℝ v v ∂μ :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg (hr i).le _)) (integral_nonneg fun y ↦
          mul_nonneg (hφ0 _) (real_inner_self_nonneg))
      have hlow := (abs_le.mp hh).1
      change -(M * ‖v‖ * e i) ≤ _ at hlow
      linarith
    exact le_of_tendsto_of_tendsto
      (by simpa only [mul_zero, neg_zero] using (he.const_mul (M * ‖v‖)).neg)
      (htest φ hφ hcφ hsφ v) hbtest

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem volumeReal_blownUpSet_closedBall {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    volume.real (blownUpSet E c r ∩ Metric.closedBall (0 : Euc n) s) =
      (r ^ n)⁻¹ * volume.real (E ∩ Metric.closedBall c (r * s)) := by
  have hi := integral_blownUpSet hE
    ((Metric.closedBall c (r * s)).indicator (fun _ ↦ (1 : ℝ))) c hr
  have he : (fun z ↦ (Metric.closedBall c (r * s)).indicator (fun _ ↦ (1 : ℝ)) (c + r • z)) =
      (Metric.closedBall (0 : Euc n) s).indicator (fun _ ↦ (1 : ℝ)) := by
    funext z
    have hm : c + r • z ∈ Metric.closedBall c (r * s) ↔ z ∈ Metric.closedBall (0 : Euc n) s := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero,
        norm_smul, Real.norm_of_nonneg hr.le]
      exact mul_le_mul_iff_right₀ hr
    by_cases hz : z ∈ Metric.closedBall (0 : Euc n) s
    · simp [hz, hm.mpr hz]
    · simp [hz, mt hm.mp hz]
  rw [he] at hi
  simpa only [integral_indicator_const _ measurableSet_closedBall,
    measureReal_restrict_apply measurableSet_closedBall, smul_eq_mul, mul_one, inter_comm] using hi

theorem indicator_L1_compl {n : ℕ} (A F : Set (Euc n)) :
    (∫⁻ x, ‖Aᶜ.indicator (fun _ ↦ (1 : ℝ)) x - Fᶜ.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) =
      ∫⁻ x, ‖A.indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ := by
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A <;> by_cases hy : x ∈ F <;> simp [hx, hy]

theorem tendsto_volumeReal_inter_closedBall_of_indicator_L1 {n : ℕ}
    (A : ℕ → Set (Euc n)) (F : Set (Euc n))
    (hA : ∀ i, MeasurableSet (A i)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0)) (c : Euc n) (s : ℝ) :
    Tendsto (fun i ↦ volume.real (A i ∩ Metric.closedBall c s)) atTop
      (𝓝 (volume.real (F ∩ Metric.closedBall c s))) := by
  have hf : Integrable ((Metric.closedBall c s).indicator (fun _ ↦ (1 : ℝ))) volume :=
    ((continuous_const.locallyIntegrable (μ := (volume : Measure (Euc n)))).integrableOn_isCompact
      (isCompact_closedBall c s)).integrable_indicator measurableSet_closedBall
  have hb : ∃ M : ℝ, ∀ x : Euc n, ‖(Metric.closedBall c s).indicator (fun _ ↦ (1 : ℝ)) x‖ ≤ M := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ Metric.closedBall c s <;> simp [hx]
  have ht := tendsto_setIntegral_of_indicator_L1 A F hA hF hconv hf hb
  simpa only [integral_indicator_const _ measurableSet_closedBall,
    measureReal_restrict_apply measurableSet_closedBall, smul_eq_mul, mul_one, inter_comm] using ht

theorem two_phase_of_indicator_L1 {n : ℕ}
    (A : ℕ → Set (Euc n)) (F : Set (Euc n))
    (hA : ∀ i, MeasurableSet (A i)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε)
    (hphase : ∀ i (s : ℝ), 0 < s → s ≤ 1 →
      ε * s ^ n ≤ volume.real (A i ∩ Metric.closedBall (0 : Euc n) s) ∧
      ε * s ^ n ≤ volume.real ((A i)ᶜ ∩ Metric.closedBall (0 : Euc n) s)) :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      0 < volume (F ∩ Metric.ball (0 : Euc n) s) ∧
      0 < volume (Fᶜ ∩ Metric.ball (0 : Euc n) s) := by
  intro s hs hs1
  have hh : 0 < s / 2 := by positivity
  have hh1 : s / 2 ≤ 1 := by linarith
  have hl : ε * (s / 2) ^ n ≤ volume.real (F ∩ Metric.closedBall (0 : Euc n) (s / 2)) := by
    apply ge_of_tendsto (tendsto_volumeReal_inter_closedBall_of_indicator_L1 A F hA hF hconv 0 (s / 2))
    exact Eventually.of_forall fun i ↦ (hphase i _ hh hh1).1
  have hconvC : Tendsto (fun i ↦ ∫⁻ x,
      ‖(A i)ᶜ.indicator (fun _ ↦ (1 : ℝ)) x - Fᶜ.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0) := by simpa only [indicator_L1_compl] using hconv
  have hlc : ε * (s / 2) ^ n ≤ volume.real (Fᶜ ∩ Metric.closedBall (0 : Euc n) (s / 2)) := by
    apply ge_of_tendsto (tendsto_volumeReal_inter_closedBall_of_indicator_L1
      (fun i ↦ (A i)ᶜ) Fᶜ (fun i ↦ (hA i).compl) hF.compl hconvC 0 (s / 2))
    exact Eventually.of_forall fun i ↦ (hphase i _ hh hh1).2
  have hp : 0 < ε * (s / 2) ^ n := mul_pos hε (pow_pos hh n)
  have hsub : Metric.closedBall (0 : Euc n) (s / 2) ⊆ Metric.ball (0 : Euc n) s :=
    Metric.closedBall_subset_ball (by linarith)
  exact ⟨(ENNReal.toReal_pos_iff.mp (hp.trans_le hl)).1.trans_le
      (measure_mono (inter_subset_inter_right F hsub)),
    (ENNReal.toReal_pos_iff.mp (hp.trans_le hlc)).1.trans_le
      (measure_mono (inter_subset_inter_right Fᶜ hsub))⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem tendsto_rescaledHalfspaceError_of_indicator_L1 {n : ℕ}
    (E : Set (Euc n)) (c v : Euc n) (r : ℕ → ℝ)
    (A : ℕ → Set (Euc n)) (hA : ∀ i, MeasurableSet (A i))
    (hAE : ∀ i, A i ∩ Metric.ball (0 : Euc n) 2 =
      blownUpSet E c (r i) ∩ Metric.ball (0 : Euc n) 2)
    (F : Set (Euc n)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0))
    (hhalf : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Euc n) 1),
      x ∈ F ↔ inner ℝ x v < 0) :
    Tendsto (fun i ↦ rescaledHalfspaceError E (r i) (c, v)) atTop (𝓝 0) := by
  have ht : Tendsto (fun i ↦ ∫⁻ x in Metric.ball (0 : Euc n) 1,
      ‖(A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ ↦ bot_le) (fun i ↦ setLIntegral_le_lintegral _ _)
  have htR := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp ht
  simp only [ENNReal.toReal_zero] at htR
  convert htR using 1
  funext i
  dsimp only [Function.comp_def]
  have hm : AEStronglyMeasurable (fun x ↦
      (A i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x)
      (volume.restrict (Metric.ball (0 : Euc n) 1)) :=
    ((measurable_const.indicator (hA i)).sub
      (measurable_const.indicator hF)).aestronglyMeasurable.restrict
  rw [← integral_norm_eq_lintegral_enorm hm]
  unfold rescaledHalfspaceError
  apply integral_congr_ae
  have hzball : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Euc n) 1),
      z ∈ Metric.ball (0 : Euc n) 1 := ae_restrict_mem measurableSet_ball
  filter_upwards [hhalf, hzball] with z hz hz1
  have hz2 := Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz1
  have hAz : z ∈ A i ↔ c + r i • z ∈ E := by
    have hh := Set.ext_iff.mp (hAE i) z
    simpa only [blownUpSet, mem_inter_iff, mem_preimage, hz2, and_true] using hh
  have hχA : (A i).indicator (fun _ ↦ (1 : ℝ)) z =
      E.indicator (fun _ ↦ (1 : ℝ)) (c + r i • z) := by
    by_cases ha : z ∈ A i
    · simp [ha, hAz.mp ha]
    · simp [ha, mt hAz.mpr ha]
  have hχF : F.indicator (fun _ ↦ (1 : ℝ)) z =
      {y | inner ℝ y v < 0}.indicator (fun _ ↦ (1 : ℝ)) z := by
    by_cases hf : z ∈ F
    · simp [hf, hz.mp hf]
    · simp [hf, mt hz.mpr hf]
  rw [hχA, hχF, Real.norm_eq_abs]

theorem tendsto_of_every_subseq_has_subseq {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (x : X)
    (h : ∀ σ : ℕ → ℕ, StrictMono σ → ∃ τ : ℕ → ℕ, StrictMono τ ∧
      Tendsto (fun i ↦ f (σ (τ i))) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  by_contra ht
  rw [tendsto_def] at ht
  push Not at ht
  obtain ⟨S, hS, hnot⟩ := ht
  have hf : ∃ᶠ i in atTop, f i ∉ S := by
    intro hevent
    apply hnot
    filter_upwards [hevent] with i hi
    exact not_not.mp hi
  obtain ⟨σ, hσ, hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨τ, hτ, hgood⟩ := h σ hσ
  obtain ⟨i, hi⟩ := (hgood.eventually hS).exists
  exact hbad (τ i) hi

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem inter_eq_on_subdomain {X : Type*} {A B U V : Set X}
    (hAB : A ∩ U = B ∩ U) (hVU : V ⊆ U) : A ∩ V = B ∩ V := by
  have hu : U ∩ V = V := inter_eq_right.mpr hVU
  calc
    A ∩ V = (A ∩ U) ∩ V := by rw [inter_assoc, hu]
    _ = (B ∩ U) ∩ V := by rw [hAB]
    _ = B ∩ V := by rw [inter_assoc, hu]

theorem compl_inter_eq_of_inter_eq {X : Type*} {A B U : Set X}
    (hAB : A ∩ U = B ∩ U) : Aᶜ ∩ U = Bᶜ ∩ U := by
  ext x
  have hh := Set.ext_iff.mp hAB x
  simp only [mem_inter_iff, mem_compl_iff] at hh ⊢
  tauto

theorem scaled_two_phase_bound_for_blownUpSet {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (c : Euc n) {ε : ℝ}
    (hden : ∀ R : ℝ, 0 < R →
      ε * R ^ n < volume.real (E ∩ Metric.closedBall c R) ∧
      ε * R ^ n < volume.real (Eᶜ ∩ Metric.closedBall c R))
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ε * s ^ n ≤ volume.real (blownUpSet E c r ∩ Metric.closedBall (0 : Euc n) s) ∧
    ε * s ^ n ≤ volume.real ((blownUpSet E c r)ᶜ ∩ Metric.closedBall (0 : Euc n) s) := by
  have he : (r ^ n)⁻¹ * (ε * (r * s) ^ n) = ε * s ^ n := by
    rw [mul_pow]
    field_simp
  have hd := hden (r * s) (mul_pos hr hs)
  constructor
  · rw [volumeReal_blownUpSet_closedBall hE c hr s, ← he]
    exact mul_le_mul_of_nonneg_left hd.1.le (by positivity)
  · change ε * s ^ n ≤ volume.real (blownUpSet Eᶜ c r ∩ Metric.closedBall (0 : Euc n) s)
    rw [volumeReal_blownUpSet_closedBall hE.compl c hr s, ← he]
    exact mul_le_mul_of_nonneg_left hd.2.le (by positivity)

theorem exists_halfspace_blowup_subsequence {n : ℕ} (hn : 1 < n)
    {E U : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hU : IsOpen U)
    (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {G : Euc n → Euc n} (hG : Integrable G μ)
    (hrep : ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ U → (∫ y in E, divergence V y) = ∫ y, inner ℝ (G y) (V y) ∂μ)
    (c v : Euc n) (hcU : c ∈ U) (hc : c ∈ perimeterSupport E) (hv : ‖v‖ = 1)
    (hosc : Tendsto (fun s : ℝ ↦ (s ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c s,
      ‖G y - v‖ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun i ↦ rescaledHalfspaceError E (r (σ i)) (c, v)) atTop (𝓝 0) := by
  have hn0 : 0 < n := lt_trans (by norm_num) hn
  obtain ⟨C, hC, hbound⟩ := exists_blownUpSet_perimeter_bound hn0
  obtain ⟨F, hF, hFK, A, hA, hAE, σ, hσ, hconv⟩ :=
    exists_local_indicator_L1_subsequence C hC (fun i ↦ blownUpSet E c (r i))
      (fun i ↦ measurableSet_blownUpSet hmin.1 c (r i))
      (fun i ↦ hbound E hmin c (r i) (hr i))
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨ε, hε, hdensity⟩ := minimizing_scaled_two_phase_volume_lower
    (Real.HolderConjugate.conjExponent hnR)
  have hphaseA : ∀ i (s : ℝ), 0 < s → s ≤ 1 →
      ε * s ^ n ≤ volume.real (A i ∩ Metric.closedBall (0 : Euc n) s) ∧
      ε * s ^ n ≤ volume.real ((A i)ᶜ ∩ Metric.closedBall (0 : Euc n) s) := by
    intro i s hs hs1
    have hsub : Metric.closedBall (0 : Euc n) s ⊆ Metric.ball (0 : Euc n) 2 :=
      Metric.closedBall_subset_ball (by linarith)
    rw [inter_eq_on_subdomain (hAE i) hsub,
      inter_eq_on_subdomain (compl_inter_eq_of_inter_eq (hAE i)) hsub]
    exact scaled_two_phase_bound_for_blownUpSet hmin.1 c
      (hdensity E hmin c hc) (hr i) hs
  have hphase : ∀ s : ℝ, 0 < s → s ≤ 1 →
      0 < volume (F ∩ Metric.ball (0 : Euc n) s) ∧
      0 < volume (Fᶜ ∩ Metric.ball (0 : Euc n) s) :=
    two_phase_of_indicator_L1 (fun i ↦ A (σ i)) F (fun i ↦ hA (σ i)) hF hconv hε
      (fun i ↦ hphaseA (σ i))
  have hrU : ∀ᶠ i in atTop, Metric.ball c (r i * 2) ⊆ U := by
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hcU)
    have ht : Tendsto (fun i ↦ r i * 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using hr0.mul_const 2
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
    exact (Metric.ball_subset_ball hi.le).trans hδU
  obtain ⟨hflat, hmono⟩ := flat_distribution_of_polar_blowup_limit hn0 hmin.1 μ hG hrep
    c v hosc (fun i ↦ hr (σ i)) (hr0.comp hσ.tendsto_atTop)
    (hσ.tendsto_atTop.eventually hrU) (fun i ↦ A (σ i)) (fun i ↦ hA (σ i))
    (fun i ↦ hAE (σ i)) F hF hconv
  obtain ⟨t, ht, hhalf⟩ := halfspace_of_flat_distribution hF (by norm_num : (0 : ℝ) < 2)
    hv hflat hmono
  have hhalf1 : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Euc n) 1),
      x ∈ F ↔ inner ℝ x v < t := by simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using hhalf
  have ht0 := halfspace_threshold_eq_zero (by norm_num : (0 : ℝ) < 1) hv hhalf1 hphase
  rw [ht0] at hhalf1
  exact ⟨σ, hσ, tendsto_rescaledHalfspaceError_of_indicator_L1 E c v (fun i ↦ r (σ i))
    (fun i ↦ A (σ i)) (fun i ↦ hA (σ i)) (fun i ↦ hAE (σ i)) F hF hconv hhalf1⟩

theorem hasHalfspaceBlowup_of_differentiating_polar {n : ℕ} (hn : 1 < n)
    {E U : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) (hU : IsOpen U)
    (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    {G : Euc n → Euc n} (hG : Integrable G μ)
    (hrep : ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ U → (∫ y in E, divergence V y) = ∫ y, inner ℝ (G y) (V y) ∂μ)
    (c v : Euc n) (hcU : c ∈ U) (hc : c ∈ perimeterSupport E) (hv : ‖v‖ = 1)
    (hosc : Tendsto (fun s : ℝ ↦ (s ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall c s,
      ‖G y - v‖ ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0)) : HasHalfspaceBlowup E c v := by
  apply (hasHalfspaceBlowup_iff_dyadic hmin.1 c v).mpr
  refine ⟨hv, tendsto_of_every_subseq_has_subseq
    (fun i : ℕ ↦ rescaledHalfspaceError E ((1 / 2 : ℝ) ^ i) (c, v)) (0 : ℝ) ?_⟩
  intro σ hσ
  have ht : Tendsto (fun i ↦ (1 / 2 : ℝ) ^ σ i) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp hσ.tendsto_atTop
  exact exists_halfspace_blowup_subsequence hn hmin hU μ hG hrep c v hcU hc hv hosc
    (r := fun i : ℕ ↦ (1 / 2 : ℝ) ^ σ i)
    (fun i ↦ pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (σ i)) ht

end RPISingularHarnack

end

end OAI
