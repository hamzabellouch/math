import OAI.Analysis.StrictMeans.BoundaryCells

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma dyadicHeight_rpow (γ : ℝ) (n : ℕ) :
    (dyadicHeight n)^γ = ((1/2 : ℝ)^γ)^n := by
  dsimp only [dyadicHeight]
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (n:ℝ), Real.rpow_mul_natCast (by norm_num)]

lemma ae_eventually_dyadic_cover {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : ℕ → Set α} {D : ℝ≥0∞} (hD : D < ⊤) {γ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ n, μ (s n) ≤ D * ENNReal.ofReal ((dyadicHeight n)^γ)) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n := by
  apply ae_eventually_notMem
  apply ne_of_lt
  calc
    (∑' n, μ (s n)) ≤ ∑' n, D * ENNReal.ofReal ((dyadicHeight n)^γ) := ENNReal.tsum_le_tsum hbound
    _ = D * (1 - ENNReal.ofReal ((1/2:ℝ)^γ))⁻¹ := by
      simp only [dyadicHeight_rpow, ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) γ),
        ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top hD (ENNReal.inv_lt_top.mpr (by
      exact tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr
        (Real.rpow_lt_one (by norm_num) (by norm_num) hγ))))

lemma dyadic_band_after {y : ℝ} (hy : 0 < y) (N : ℕ) (hNy : y < dyadicHeight N) :
    ∃ n : ℕ, N ≤ n ∧ dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  have hy1 : y ≤ 1 := hNy.le.trans (dyadicHeight_le_one N)
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨m+1, ?_, hmlo.le, ?_⟩
  · by_contra hh
    have hmN : m+1 ≤ N := le_of_lt (lt_of_not_ge hh)
    have hp : dyadicHeight N ≤ dyadicHeight (m+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hmN
    exact (hNy.trans_le hp).not_ge hmlo.le
  · dsimp [dyadicHeight]
    rw [pow_succ]
    linarith

def boundaryEscape (k : ℝ) (F : ℂ → ℂ) (ξ : ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ z : UpperHalfPlane,
    z.im < ε → z.im^k/δ < ‖F z-ξ‖

lemma boundaryBadScale_ae_eventually (f : DiskFamily) (β k R δ : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hδ : 0 < δ) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ∀ᶠ n in atTop, ξ ∉ boundaryBadScale f k R δ (dyadicHeight n) := by
  obtain ⟨D,hD,hbound⟩ := boundaryBadScale_measure_bound f β k R δ hβ (by linarith) hδ hfin
  exact ae_eventually_dyadic_cover volume hD (by linarith : 0 < 2*k-1)
    (fun n => hbound _ (dyadicHeight_pos n) (dyadicHeight_le_one n))

theorem ae_omitted_boundary_escape (f : DiskFamily) (β k : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im} →
      boundaryEscape k (halfPlaneFunction f) ξ := by
  have hall : ∀ᵐ ξ : ℂ, ∀ m n : ℕ, ∀ᶠ j in atTop,
      ξ ∉ boundaryBadScale f k (m:ℝ) (1/(n+1)) (dyadicHeight j) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro n
    exact boundaryBadScale_ae_eventually f β k m (1/(n+1)) hβ hk (by positivity) hfin
  filter_upwards [hall] with ξ hξ
  intro homit δ hδ
  obtain ⟨m,hm⟩ := exists_nat_gt ‖ξ‖
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hξ m n)
  refine ⟨dyadicHeight N, dyadicHeight_pos N, fun z hz => ?_⟩
  obtain ⟨j,hj,hjlo,hjhi⟩ := dyadic_band_after z.im_pos N hz
  by_contra hbad
  apply hN j hj
  refine ⟨z, homit, hm.le, hjlo, hjhi, ?_⟩
  calc
    ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ := le_of_not_gt hbad
    _ ≤ z.im^k/(1/(n+1:ℝ)) := by gcongr

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma image_target_separated_near_boundary (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) :
    ∃ ε a : ℝ, 0 < ε ∧ 0 < a ∧ ∀ z : UpperHalfPlane,
      z.im < ε → a ≤ ‖halfPlaneFunction f z - ξ‖ := by
  obtain ⟨w,hw,rfl⟩ := hξ
  change 0 < w.im at hw
  let r : ℝ := w.im/2
  have hr : 0 < r := half_pos hw
  have hsub : ball w r ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have he := im_lower_of_mem_ball hz
    change 0 < z.im
    dsimp [r] at he
    linarith
  have hd := (halfPlaneFunction_differentiableOn f).mono hsub
  have hi := (halfPlaneFunction_injOn f).mono hsub
  have hn := halfPlaneFunction_deriv_ne_zero f hw
  have hq := local_koebe_quarter hr hd hi hn
  refine ⟨r, r * ‖deriv (halfPlaneFunction f) w‖ / 4, hr,
    div_pos (mul_pos hr (norm_pos_iff.mpr hn)) (by norm_num), ?_⟩
  intro z hz
  by_contra he
  have hzball : halfPlaneFunction f z ∈
      ball (halfPlaneFunction f w) (r * ‖deriv (halfPlaneFunction f) w‖ /4) := by
    simpa only [mem_ball, dist_eq_norm] using lt_of_not_ge he
  obtain ⟨u,hu,heu⟩ := hq hzball
  have huz : u = z := halfPlaneFunction_injOn f (hsub hu) z.im_pos heu
  rw [huz] at hu
  have he := im_lower_of_mem_ball hu
  change w.im-r < z.im at he
  dsimp [r] at he hz
  linarith

lemma image_target_boundary_escape (f : DiskFamily) {k : ℝ} (hk : 0 < k) {ξ : ℂ}
    (hξ : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) :
    boundaryEscape k (halfPlaneFunction f) ξ := by
  obtain ⟨ε,a,hε,ha,hsep⟩ := image_target_separated_near_boundary f hξ
  intro δ hδ
  have hc : ContinuousAt (fun y : ℝ => y^k / δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he : ∀ᶠ y : ℝ in 𝓝 0, y^k/δ < a :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by simpa [Real.zero_rpow hk.ne'] using ha))
  obtain ⟨η,hη,hb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min ε η, lt_min hε hη, fun z hz => ?_⟩
  have hzη : (z.im : ℝ) ∈ ball 0 η := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos z.im_pos]
      using (lt_of_lt_of_le hz (min_le_right _ _))
  exact (hb hzη).trans_le (hsep z (lt_of_lt_of_le hz (min_le_left _ _)))

lemma ae_boundary_escape (f : DiskFamily) (β k : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, boundaryEscape k (halfPlaneFunction f) ξ := by
  filter_upwards [ae_omitted_boundary_escape f β k hβ hk hfin] with ξ hξ
  by_cases hi : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}
  · exact image_target_boundary_escape f (by linarith) hi
  · exact hξ hi

lemma norm_image_at_infinity_in_strip (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ᶠ a in l, ε ≤ (Z a).im)
    (hnorm : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => ‖halfPlaneFunction f (Z a)‖) l atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨M,hM⟩ := bounded_strip_preimage f β hβ hfin (ε := ε) (R := R) hε
  filter_upwards [hstrip, hnorm.eventually_gt_atTop M] with a ha ham
  by_contra h
  exact (hM (Z a) ha (le_of_not_ge h)).not_gt ham

lemma translated_escape_at_infinity_in_strip (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ᶠ a in l, ε ≤ (Z a).im)
    (hnorm : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => (Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)-ξ‖) l (𝓝 0) := by
  have he := escape_at_infinity f β hβ hfin Z hnorm
  have hf := norm_image_at_infinity_in_strip f β hβ hfin Z hε hstrip hnorm
  have hb : ∀ᶠ a in l, (Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)-ξ‖ ≤
      2*((Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)‖) := by
    filter_upwards [hf.eventually_gt_atTop (2*‖ξ‖+1)] with a ha
    have hn := norm_sub_norm_le (halfPlaneFunction f (Z a)) ξ
    have hF : 0 < ‖halfPlaneFunction f (Z a)‖-‖ξ‖ := by linarith [norm_nonneg ξ]
    have hd : 0 < ‖halfPlaneFunction f (Z a)-ξ‖ := hF.trans_le hn
    rw [div_le_iff₀ hd]
    have hp : 0 < ‖halfPlaneFunction f (Z a)‖ := by linarith [norm_nonneg ξ]
    have ht : 2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖ ≥ 1 := by
      change 1 ≤ 2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖
      rw [le_div_iff₀ hp]
      linarith
    have ht' := mul_le_mul_of_nonneg_left ht
      (Real.rpow_nonneg (Z a).im_pos.le ((β+2)/3))
    nlinarith [show (Z a).im ^ ((β+2)/3) * (2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖) =
      2*((Z a).im ^ ((β+2)/3)/‖halfPlaneFunction f (Z a)‖)*‖halfPlaneFunction f (Z a)-ξ‖ by ring]
  apply squeeze_zero' (Eventually.of_forall (fun a => div_nonneg (Real.rpow_nonneg (Z a).im_pos.le _) (norm_nonneg _))) hb
  simpa using he.const_mul 2

def potentialSuperlevel (k : ℝ) (F : ℂ → ℂ) (ξ : ℂ) (h : ℝ) : Set ℂ :=
  {z | 0 < z.im ∧ ‖F z - ξ‖ ≤ z.im ^ k / h}

lemma bounded_strip_superlevel (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : UpperHalfPlane, ε ≤ z.im →
      ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ → ‖(z:ℂ)‖ ≤ M := by
  by_contra h
  push Not at h
  choose Z hZ using fun n : ℕ => h (n:ℝ)
  have hn : Tendsto (fun n => ‖(Z n : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hZ n).2.2.le) tendsto_natCast_atTop_atTop
  have he := translated_escape_at_infinity_in_strip f β hβ hfin ξ Z hε
    (Eventually.of_forall (fun n => (hZ n).1)) hn
  have hF := norm_image_at_infinity_in_strip f β hβ hfin Z hε
    (Eventually.of_forall (fun n => (hZ n).1)) hn
  have hlo : ∀ᶠ n in atTop, δ ≤ (Z n).im^((β+2)/3)/‖halfPlaneFunction f (Z n)-ξ‖ := by
    filter_upwards [hF.eventually_gt_atTop ‖ξ‖] with n hh
    have hd : 0 < ‖halfPlaneFunction f (Z n)-ξ‖ :=
      (sub_pos.mpr hh).trans_le (norm_sub_norm_le _ _)
    rw [le_div_iff₀ hd]
    have h := (le_div_iff₀ hδ).mp (hZ n).2.1
    linarith
  exact hδ.not_ge (ge_of_tendsto he hlo)

lemma compact_superlevels_of_boundary_escape (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ)
    (hescape : boundaryEscape ((β+2)/3) (halfPlaneFunction f) ξ) {δ : ℝ} (hδ : 0 < δ) :
    IsCompact (potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ) := by
  obtain ⟨ε,hε,hbound⟩ := hescape δ hδ
  have heq : potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ =
      {z : ℂ | ε ≤ z.im ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ} := by
    ext z
    constructor
    · intro hz
      refine ⟨?_,hz.2⟩
      by_contra hh
      exact (hbound ⟨z,hz.1⟩ (lt_of_not_ge hh)).not_ge hz.2
    · intro hz
      exact ⟨hε.trans_le hz.1,hz.2⟩
  rw [heq]
  have hclosed : IsClosed {z : ℂ | ε ≤ z.im ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ} := by
    apply (isClosed_le continuous_const Complex.continuous_im).isClosed_le
    · have hc : ContinuousOn (halfPlaneFunction f) {z : ℂ | ε ≤ z.im} :=
        (halfPlaneFunction_differentiableOn f).continuousOn.mono (fun z hz => hε.trans_le hz)
      exact (hc.sub continuousOn_const).norm
    · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ (β+2)/3)).comp Complex.continuous_im).continuousOn.div_const δ
  obtain ⟨M,hM⟩ := bounded_strip_superlevel f β hβ hfin ξ hε hδ
  apply (isCompact_closedBall (0:ℂ) M).of_isClosed_subset hclosed
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using hM ⟨z,hε.trans_le hz.1⟩ hz.1 hz.2

theorem ae_compact_positive_superlevels (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      IsCompact (potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ) := by
  filter_upwards [ae_boundary_escape f β ((β+2)/3) hβ (by linarith) hfin] with ξ hξ
  exact fun δ hδ => compact_superlevels_of_boundary_escape f β hβ hfin ξ hξ hδ

theorem affine_law_ae_compact_superlevels (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      IsCompact (potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ) := by
  filter_upwards [weightedAreaTail_ae_finite μ β hlaw] with f hf
  exact ae_compact_positive_superlevels f β hβ hf

end
end StrictInverseFirstPower

end

end OAI
