import OAI.Geometry.Perimeter.Regularity.FlatExcess

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem tendsto_phase_slab_error {E : ℕ → Set (Euc n)}
    (hE : ∀ i, MeasurableSet (E i)) {v : Euc n} (hv : ‖v‖=1)
    (a : ℕ → ℝ) (hat : Tendsto a atTop (𝓝 0)) (R : ℝ)
    (hphase : ∀ i, ∀ᵐ x ∂volume, x∈Metric.ball 0 R → a i < |inner ℝ v x| →
      (x∈E i ↔ inner ℝ v x<0)) :
    Tendsto (fun i ↦ volume.real (symmDiff (E i) {x | inner ℝ x v<0} ∩ Metric.ball 0 R))
      atTop (𝓝 0) := by
  let H : Set (Euc n) := {x | inner ℝ x v<0}
  have hH : MeasurableSet H := (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  let f := fun i x ↦ |(E i).indicator (fun _ ↦ (1:ℝ)) x-H.indicator (fun _ ↦ (1:ℝ)) x|
  have hmeas (i) : AEStronglyMeasurable (f i) (volume.restrict (Metric.ball 0 R)) :=
    (((measurable_const.indicator (hE i)).sub (measurable_const.indicator hH)).abs).aestronglyMeasurable.restrict
  have hb (i) : ∀ᵐ x ∂volume.restrict (Metric.ball (0:Euc n) R), ‖f i x‖≤1 := by
    apply ae_of_all
    intro x
    by_cases hx : x∈E i <;> by_cases hy : x∈H <;> simp [f,hx,hy]
  have hn : (innerSL ℝ v : Euc n →L[ℝ] ℝ) ≠ 0 := by
    intro hz
    have he := congrArg (fun L : Euc n →L[ℝ] ℝ ↦ L v) hz
    change inner ℝ v v=0 at he
    rw [real_inner_self_eq_norm_sq,hv] at he
    norm_num at he
  have hall := ae_all_iff.mpr hphase
  have ht : ∀ᵐ x ∂volume.restrict (Metric.ball (0:Euc n) R), Tendsto (fun i ↦ f i x) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hall,ae_restrict_of_ae (ae_linear_ne_zero hn),
      ae_restrict_mem measurableSet_ball] with x hx hnz hxB
    apply tendsto_const_nhds.congr'
    have hpos : 0 < |inner ℝ v x| := abs_pos.mpr hnz
    filter_upwards [hat.eventually (gt_mem_nhds hpos)] with i hi
    have hm := hx i hxB hi
    have hm' : x∈E i ↔ x∈H := by simpa only [H,mem_ofPred_eq,real_inner_comm x v] using hm
    by_cases he : x∈E i
    · simp [f,he,hm'.mp he]
    · simp [f,he,mt hm'.mpr he]
  have ht' := tendsto_integral_of_dominated_convergence (fun _ : Euc n ↦ (1:ℝ)) hmeas
    (integrableOn_const measure_ball_lt_top.ne) hb ht
  simp only [integral_zero] at ht'
  convert ht' using 1
  ext i
  exact (integral_abs_indicator_sub_eq_symmDiff (hE i) hH).symm

theorem tendsto_setIntegral_of_ball_symmDiff {E : ℕ → Set (Euc n)} {F : Set (Euc n)}
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F) {R : ℝ}
    (hconv : Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.ball 0 R)) atTop (𝓝 0))
    {f : Euc n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Metric.ball 0 R) :
    Tendsto (fun i ↦ ∫ x in E i, f x) atTop (𝓝 (∫ x in F, f x)) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  have hC0 : 0≤C := (norm_nonneg (f 0)).trans (hC 0)
  have hb (i) := abs_setIntegral_sub_le_symmDiff_volume (hE i) hF measurableSet_ball
    measure_ball_lt_top.ne (hf.integrable_of_hasCompactSupport hc)
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))) hC0
    (fun x ↦ by simpa only [Real.norm_eq_abs] using hC x)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i ↦ norm_nonneg _)
    (fun i ↦ by simpa only [Real.norm_eq_abs] using hb i)
  simpa using hconv.const_mul C

theorem orientedTilt_tendsto_of_local_halfspace_L1 (hn : 1<n)
    {E : ℕ → Set (Euc n)} (hmin : ∀ i, IsLocallyPerimeterMinimizing (E i))
    {v : Euc n} (hv : ‖v‖=1)
    (hH : IsLocallyPerimeterMinimizing {x : Euc n | inner ℝ x v<0})
    (hconv : Tendsto (fun i ↦ volume.real
      (symmDiff (E i) {x | inner ℝ x v<0} ∩ Metric.ball 0 8)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ orientedTilt (E i) v (Metric.ball 0 4)) atTop (𝓝 0) := by
  let H : Set (Euc n) := {x | inner ℝ x v<0}
  apply tendsto_order.2
  constructor
  · intro A hA
    exact Eventually.of_forall fun i ↦ hA.trans_le (integral_nonneg fun _ ↦ sq_nonneg _)
  · intro ε hε
    obtain ⟨η,hη,hcη,hsη,hbη,honeη,hcal⟩ := exists_halfspace_calibration hn hv hH
      (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)<6) (by positivity : 0<ε/8)
    obtain ⟨a₀,ha₀,hs₀⟩ := exists_lt_subset_ball (isClosed_tsupport η) hsη
    let b := max a₀ 5
    have h4b : 4<b := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hb6 : b<6 := max_lt ha₀ (by norm_num)
    have hb : 0<b := lt_trans (by norm_num) h4b
    have hsb : tsupport η ⊆ Metric.ball 0 b := hs₀.trans (Metric.ball_subset_ball (le_max_left _ _))
    have hann : Tendsto (fun i ↦ volume.real (symmDiff (E i) H ∩
        (Metric.closedBall 0 6 \ Metric.closedBall 0 b))) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun i ↦ ?_) hconv
      apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
      exact inter_subset_inter_right _ (sdiff_subset.trans (Metric.closedBall_subset_ball (by norm_num : (6:ℝ)<8)))
    have hmass := eventually_minimizing_perimeter_le_of_annular_L1 hmin hH.1 0 hb hb6 hann
      (by positivity : 0<ε/8)
    have hflux := tendsto_setIntegral_of_ball_symmDiff (f := divergence (fun y ↦ η y • v)) (fun i ↦ (hmin i).1) hH.1 hconv
      (continuous_divergence (hη.smul contDiff_const))
      (hcη.smul_right.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset _))
      ((tsupport_divergence_subset _).trans ((tsupport_smul_subset_left _ _).trans
        (hsη.trans (Metric.ball_subset_ball (by norm_num : (6:ℝ)≤8)))))
    have hfl := hflux.eventually (lt_mem_nhds (sub_lt_self _ (by positivity : 0<ε/8)))
    filter_upwards [hmass,hfl] with i hi hfi
    have hm : (perimeter (E i) (Metric.ball 0 b)).toReal ≤
        (perimeter H (Metric.ball 0 6)).toReal+ε/8 := by
      have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(hH.2.1 0 6 (by norm_num)).ne,
        ENNReal.ofReal_ne_top⟩) hi
      rwa [ENNReal.toReal_add (hH.2.1 0 6 (by norm_num)).ne ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by positivity : 0≤ε/8)] at ht
    have hgap := orientedTilt_le_calibration_gap hn (hmin i) hv (by norm_num : (0:ℝ)<4)
      h4b hη hcη hsb hbη honeη
    change (perimeter H (Metric.ball 0 6)).toReal-ε/8 < _ at hcal
    linarith

end RPISingularHarnack

end

end OAI
