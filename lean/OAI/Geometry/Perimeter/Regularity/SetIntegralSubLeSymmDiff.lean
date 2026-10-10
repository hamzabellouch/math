import OAI.Geometry.Perimeter.Regularity.PerimeterAdmissiblePartitionPiece

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
open scoped ENNReal Topology ContDiff
open scoped Topology ENNReal
namespace RPISingularHarnack

theorem setIntegral_sub_le_symmDiff {n : ℕ} {E F : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) {f g : Euc n → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : ∀ x, |f x| ≤ g x) :
    (∫ x in F, f x) - (∫ x in E, f x) ≤ ∫ x in symmDiff E F, g x := by
  rw [← integral_indicator hF, ← integral_indicator hE,
    ← integral_sub (hf.indicator hF) (hf.indicator hE),
    ← integral_indicator (hE.symmDiff hF)]
  apply integral_mono ((hf.indicator hF).sub (hf.indicator hE))
    (hg.indicator (hE.symmDiff hF))
  intro x
  by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F
  · simp [hxE, hxF, mem_symmDiff]
  · simpa [hxE, hxF, mem_symmDiff] using (neg_le_abs (f x)).trans (hfg x)
  · simpa [hxE, hxF, mem_symmDiff] using (le_abs_self (f x)).trans (hfg x)
  · simp [hxE, hxF, mem_symmDiff]

theorem integral_smooth_patch_le {n : ℕ} {E F U : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {V : Euc n → Euc n} (hV : PerimeterAdmissible U V)
    {c : Euc n} {r a b B : ℝ} (ha : 0 < a) (hra : r < a) (hab : a < b)
    (hbB : b < B) (hPE : perimeter E (U \ Metric.closedBall c r) ≠ ⊤)
    (hPF : perimeter F (Metric.ball c B) ≠ ⊤) :
    (∫ x in F, divergence V x) +
        (∫ x in E, annularCutoff c a b x * divergence V x) -
        (∫ x in F, annularCutoff c a b x * divergence V x) ≤
      (perimeter E (U \ Metric.closedBall c r)).toReal +
      (perimeter F (Metric.ball c B)).toReal +
        ∫ x in symmDiff E F, ‖gradient (annularCutoff c a b) x‖ := by
  have hVE : PerimeterAdmissible (U \ Metric.closedBall c r)
      (fun x ↦ annularCutoff c a b x • V x) :=
    annularCutoff_test_admissible hV ha hra hab
  have hVu : PerimeterAdmissible univ V :=
    ⟨hV.1, hV.2.1, subset_univ _, hV.2.2.2⟩
  have hVF := pairedCutTest_admissible hVu (perimeterAdmissible_zero (Metric.ball c B))
    ha hab (Metric.closedBall_subset_ball hbB)
  have hd := integrable_divergence hV.1 hV.2.1
  have hg : Integrable (fun x ↦ ‖gradient (annularCutoff c a b) x‖) volume :=
    ((gradient_annularCutoff_continuous c a b).integrable_of_hasCompactSupport
      (gradient_annularCutoff_compact c ha hab)).norm
  have hinner (x : Euc n) : |inner ℝ (gradient (annularCutoff c a b) x) (V x)| ≤
      ‖gradient (annularCutoff c a b) x‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hV.2.2.2 x))
  have hi : Integrable (fun x ↦ inner ℝ (gradient (annularCutoff c a b) x) (V x)) volume :=
    hg.mono' ((gradient_annularCutoff_continuous c a b).inner hV.1.continuous).aestronglyMeasurable
      (Eventually.of_forall hinner)
  have hmul := integrable_annularCutoff_mul hd c a b
  have hEi := integral_divergence_le_perimeter_real E _ hPE hVE
  have hFi := integral_divergence_le_perimeter_real F _ hPF hVF
  simp_rw [divergence_smul ((annularCutoff_contDiff c a b).differentiable (by simp))
    (hV.1.differentiable (by simp))] at hEi
  rw [integral_add hmul.integrableOn hi.integrableOn] at hEi
  have hformula (x : Euc n) : divergence (pairedCutTest c a b V (fun _ ↦ 0)) x =
      divergence V x - annularCutoff c a b x * divergence V x -
        inner ℝ (gradient (annularCutoff c a b) x) (V x) := by
    rw [divergence_pairedCutTest hV.1 contDiff_const]
    have hz : divergence (fun _ : Euc n ↦ (0:Euc n)) x = 0 := by simp [divergence]
    simp only [hz, zero_sub, inner_neg_right]
    ring
  simp_rw [hformula] at hFi
  have hleft : Integrable (fun x ↦ divergence V x - annularCutoff c a b x * divergence V x) volume := hd.sub hmul
  rw [integral_sub hleft.integrableOn hi.integrableOn,
    integral_sub hd.integrableOn hmul.integrableOn] at hFi
  have herr := setIntegral_sub_le_symmDiff hE hF hi hg hinner
  linarith

def gluedFilledSet {n : ℕ} (E F : Set (Euc n)) (c : Euc n) (r : ℝ) : Set (Euc n) :=
  (F ∩ Metric.closedBall c r) ∪ (E \ Metric.closedBall c r)

theorem controlled_radius_glued_perimeter_le {n : ℕ} {E F U : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (c : Euc n) {r B D L : ℝ}
    (hr : 0 < r) (hrB : r < B)
    (hcontrol : ∀ t ∈ Icc r B,
      volume.real (symmDiff E F ∩ Metric.closedBall c t) -
        volume.real (symmDiff E F ∩ Metric.closedBall c r) ≤ D * (t - r))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hPE : perimeter E (U \ Metric.closedBall c r) ≠ ⊤)
    (hPF : perimeter F (Metric.ball c B) ≠ ⊤) :
    perimeter (gluedFilledSet E F c r) U ≤
      perimeter E (U \ Metric.closedBall c r) + perimeter F (Metric.ball c B) +
        ENNReal.ofReal (4*L*D) := by
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  have hd := integrable_divergence hV.1 hV.2.1
  have hdis : Disjoint (F ∩ Metric.closedBall c r) (E \ Metric.closedBall c r) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hy.2 hx.2
  have hsplit := integral_inter_add_sdiff (s := F) (t := Metric.closedBall c r)
    measurableSet_closedBall hd.integrableOn
  have hpatch : (∫ x in F, divergence V x) +
      (∫ x in E \ Metric.closedBall c r, divergence V x) -
      (∫ x in F \ Metric.closedBall c r, divergence V x) =
      ∫ x in gluedFilledSet E F c r, divergence V x := by
    rw [gluedFilledSet, setIntegral_union hdis (hE.diff measurableSet_closedBall)
      hd.integrableOn hd.integrableOn]
    linarith
  have ht := ((tendsto_const_nhds (x := ∫ x in F, divergence V x)).add
    (tendsto_integral_annularCutoff_mul (E := E) hd c hr)).sub
      (tendsto_integral_annularCutoff_mul (E := F) hd c hr)
  rw [hpatch] at ht
  have hreal : (∫ x in gluedFilledSet E F c r, divergence V x) ≤
      (perimeter E (U \ Metric.closedBall c r)).toReal +
      (perimeter F (Metric.ball c B)).toReal + 4*L*D := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show (0:ℝ) < (B-r)/2 by linarith))] with δ hδ hsmall
    change 0 < δ at hδ
    change δ < (B-r)/2 at hsmall
    have hh := integral_smooth_patch_le hE hF hV
      (show 0 < r+δ by positivity) (show r < r+δ by linarith)
      (show r+δ < r+2*δ by linarith) (show r+2*δ < B by linarith) hPE hPF
    have hg := controlled_radius_gradient_bound (hE.symmDiff hF) c hr hδ
      (show r+2*δ ≤ B by linarith) hcontrol hD hL hbound
    linarith
  calc
    _ ≤ ENNReal.ofReal ((perimeter E (U \ Metric.closedBall c r)).toReal +
        (perimeter F (Metric.ball c B)).toReal + 4*L*D) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hPE, ENNReal.ofReal_toReal hPF]

theorem minimizing_controlled_replacement_perimeter_le {n : ℕ} {E F : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hF : MeasurableSet F)
    (c : Euc n) {a r B D L : ℝ} (ha : 0 < a) (har : a ≤ r) (hrB : r < B)
    (hcontrol : ∀ t ∈ Icc r B,
      volume.real (symmDiff E F ∩ Metric.closedBall c t) -
        volume.real (symmDiff E F ∩ Metric.closedBall c r) ≤ D*(t-r))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L)
    (hPF : perimeter F (Metric.ball c B) ≠ ⊤) :
    perimeter E (Metric.ball c a) ≤ perimeter F (Metric.ball c B) + ENNReal.ofReal (4*L*D) := by
  let U := Metric.ball c (B+1)
  let G := gluedFilledSet E F c r
  have hr : 0 < r := ha.trans_le har
  have hUfin : perimeter E U ≠ ⊤ := (hmin.2.1 c (B+1) (by linarith)).ne
  have hPE : perimeter E (U \ Metric.closedBall c r) ≠ ⊤ :=
    ne_top_of_le_ne_top hUfin (raw_perimeter_mono_region E sdiff_subset)
  have hG : MeasurableSet G :=
    (hF.inter measurableSet_closedBall).union (hmin.1.diff measurableSet_closedBall)
  have hcl : closure (symmDiff E G) ⊆ Metric.closedBall c r := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hb
    have hmem : x ∈ G ↔ x ∈ E := by simp [G, gluedFilledSet, hb]
    rcases hx with hx | hx
    · exact hx.2 (hmem.mpr hx.1)
    · exact hx.2 (hmem.mp hx.1)
  have hcmp := hmin.2.2 c (B+1) (by linarith) G hG
    ((isCompact_closedBall c r).of_isClosed_subset isClosed_closure hcl)
    (hcl.trans (Metric.closedBall_subset_ball (by linarith)))
  have hcut := controlled_radius_glued_perimeter_le hmin.1 hF c hr hrB
    hcontrol hD hL hbound hPE hPF
  have hdis : Disjoint (Metric.ball c a) (U \ Metric.closedBall c r) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hy.2 ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall har)) hx)
  have hadd := perimeter_disjoint_superadditive E
    (Metric.ball_subset_ball (by linarith : a ≤ B+1)) sdiff_subset hdis
  have hh : perimeter E (Metric.ball c a) + perimeter E (U \ Metric.closedBall c r) ≤
      (perimeter F (Metric.ball c B) + ENNReal.ofReal (4*L*D)) +
        perimeter E (U \ Metric.closedBall c r) := by
    calc
      _ ≤ perimeter E U := hadd
      _ ≤ perimeter G U := hcmp
      _ ≤ _ := by simpa only [add_assoc, add_comm, add_left_comm] using hcut
  exact (ENNReal.add_le_add_iff_right hPE).mp hh

theorem exists_controlled_annular_cut_radius {n : ℕ} {T : Set (Euc n)}
    (hT : MeasurableSet T) (c : Euc n) {a B D : ℝ} (ha : 0 < a) (haB : a < B)
    (hv : volume.real (T ∩ (Metric.closedBall c B \ Metric.closedBall c a)) < D*(B-a)) :
    ∃ r ∈ Ico a B, ∀ t ∈ Icc r B,
      volume.real (T ∩ Metric.closedBall c t) - volume.real (T ∩ Metric.closedBall c r) ≤ D*(t-r) := by
  let S := T \ Metric.closedBall c a
  have hvol : volume.real (S ∩ Metric.closedBall c B) < D*(B-a) := by
    convert hv using 2
    ext x
    simp only [S, mem_inter_iff, Set.mem_sdiff]
    tauto
  obtain ⟨r, hr, hc⟩ := exists_controlled_cut_radius S c ha haB hvol
  have he (t : ℝ) (hat : a ≤ t) :
      volume.real (S ∩ Metric.closedBall c t) =
      volume.real (T ∩ Metric.closedBall c t) - volume.real (T ∩ Metric.closedBall c a) := by
    have hset : S ∩ Metric.closedBall c t =
        (T ∩ Metric.closedBall c t) \ (T ∩ Metric.closedBall c a) := by
      ext x
      simp only [S, mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [hset]
    exact measureReal_sdiff (inter_subset_inter_right T (Metric.closedBall_subset_closedBall hat))
      (hT.inter measurableSet_closedBall)
      (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c t).measure_ne_top)
  refine ⟨r, hr, ?_⟩
  intro t ht
  have hh := hc t ht
  rw [he t (hr.1.trans ht.1), he r hr.1] at hh
  linarith

theorem minimizing_annular_replacement_perimeter_le {n : ℕ} {E F : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hF : MeasurableSet F)
    (c : Euc n) {a B D L : ℝ} (ha : 0 < a) (haB : a < B)
    (hv : volume.real (symmDiff E F ∩ (Metric.closedBall c B \ Metric.closedBall c a)) < D*(B-a))
    (hD : 0 ≤ D) (hL : 0 < L)
    (hbound : ∀ s, |deriv Real.smoothTransition s| ≤ L) :
    perimeter E (Metric.ball c a) ≤ perimeter F (Metric.ball c B) + ENNReal.ofReal (4*L*D) := by
  by_cases hPF : perimeter F (Metric.ball c B) = ⊤
  · simp [hPF]
  obtain ⟨r, hr, hc⟩ := exists_controlled_annular_cut_radius (hmin.1.symmDiff hF) c ha haB hv
  exact minimizing_controlled_replacement_perimeter_le hmin hF c ha hr.1 hr.2
    hc hD hL hbound hPF

theorem eventually_minimizing_perimeter_le_of_annular_L1 {n : ℕ}
    {E : ℕ → Set (Euc n)} {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : MeasurableSet F)
    (c : Euc n) {a B : ℝ} (ha : 0 < a) (haB : a < B)
    (hconv : Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩
      (Metric.closedBall c B \ Metric.closedBall c a))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, perimeter (E i) (Metric.ball c a) ≤
      perimeter F (Metric.ball c B) + ENNReal.ofReal ε := by
  obtain ⟨L, hL, hbound⟩ := exists_smoothTransition_deriv_bound
  let D := ε/(4*L)
  have hD : 0 < D := div_pos hε (by positivity)
  have hd : 0 < D*(B-a) := mul_pos hD (sub_pos.mpr haB)
  filter_upwards [hconv.eventually (gt_mem_nhds hd)] with i hi
  have hh := minimizing_annular_replacement_perimeter_le (hE i) hF c ha haB hi
    hD.le hL hbound
  have he : 4*L*D = ε := by dsimp [D]; field_simp
  simpa only [he] using hh

theorem lintegral_indicator_difference {n : ℕ} {E F U : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫⁻ x in U, ‖E.indicator (fun _ ↦ (1:ℝ)) x - F.indicator (fun _ ↦ (1:ℝ)) x‖ₑ) =
      volume (symmDiff E F ∩ U) := by
  have he (x : Euc n) :
      ‖E.indicator (fun _ ↦ (1:ℝ)) x - F.indicator (fun _ ↦ (1:ℝ)) x‖ₑ =
      (symmDiff E F).indicator (fun _ ↦ (1:ℝ≥0∞)) x := by
    by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE, hxF, mem_symmDiff]
  simp_rw [he]
  rw [lintegral_indicator (hE.symmDiff hF), lintegral_one,
    Measure.restrict_apply_univ, Measure.restrict_apply (hE.symmDiff hF)]

theorem abs_setIntegral_sub_le_symmDiff_volume {n : ℕ} {E F U : Set (Euc n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (hU : MeasurableSet U)
    (hUfin : volume U ≠ ⊤) {f : Euc n → ℝ} (hf : Integrable f volume)
    (hs : ∀ x ∉ U, f x = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    |(∫ x in E, f x) - (∫ x in F, f x)| ≤
      C * volume.real (symmDiff E F ∩ U) := by
  let g := U.indicator (fun _ : Euc n ↦ C)
  have hg : Integrable g volume := (integrable_indicator_iff hU).2 (integrableOn_const hUfin)
  have hfg (x : Euc n) : |f x| ≤ g x := by
    by_cases hx : x ∈ U
    · simpa [g, hx] using hb x
    · rw [hs x hx, abs_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ hC) x
  have hi : (∫ x in symmDiff E F, g x) = C * volume.real (symmDiff E F ∩ U) := by
    rw [show g = U.indicator (fun _ : Euc n ↦ C) from rfl, integral_indicator hU,
      Measure.restrict_restrict hU, integral_const, smul_eq_mul]
    rw [Set.inter_comm U (symmDiff E F)]
    simp [Measure.real, mul_comm]
  have h₁ := setIntegral_sub_le_symmDiff hE hF hf hg hfg
  have h₂ := setIntegral_sub_le_symmDiff hF hE hf hg hfg
  rw [symmDiff_comm F E, hi] at h₂
  rw [hi] at h₁
  exact abs_le.mpr ⟨by linarith, h₂⟩

theorem tendsto_setIntegral_of_local_symmDiff {n : ℕ}
    {E : ℕ → Set (Euc n)} {F : Set (Euc n)}
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F)
    (hconv : ∀ (c : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall c R)) atTop (𝓝 0))
    {f : Euc n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun i ↦ ∫ x in E i, f x) atTop (𝓝 (∫ x in F, f x)) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:Euc n)).mp hc.isBounded
  let R := max r 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : tsupport f ⊆ Metric.closedBall (0:Euc n) R :=
    hr.trans (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith [le_max_left r 0])))
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hb (i : ℕ) := abs_setIntegral_sub_le_symmDiff_volume (hE i) hF
    measurableSet_closedBall (isCompact_closedBall (0:Euc n) R).measure_ne_top
    (hf.integrable_of_hasCompactSupport hc)
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))) hC0
    (fun x ↦ by simpa only [Real.norm_eq_abs] using hC x)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i ↦ norm_nonneg _) (fun i ↦ by simpa only [Real.norm_eq_abs] using hb i)
  simpa using (hconv 0 R hR).const_mul C

theorem perimeter_le_of_eventually_le_of_local_L1 {n : ℕ}
    {E : ℕ → Set (Euc n)} {F U : Set (Euc n)}
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F)
    (hconv : ∀ (c : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall c R)) atTop (𝓝 0))
    {A : ℝ≥0∞} (hb : ∀ᶠ i in atTop, perimeter (E i) U ≤ A) :
    perimeter F U ≤ A := by
  by_cases hA : A = ⊤
  · simp [hA]
  rw [perimeter_eq_iSup_tests]
  refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
  have hc := hV.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset V)
  have ht := tendsto_setIntegral_of_local_symmDiff hE hF hconv (continuous_divergence hV.1) hc
  apply (ENNReal.ofReal_le_iff_le_toReal hA).2
  apply le_of_tendsto ht
  filter_upwards [hb] with i hi
  exact (integral_divergence_le_perimeter_real (E i) U
    (ne_top_of_le_ne_top hA hi) hV).trans (ENNReal.toReal_mono hA hi)

theorem locally_minimizing_of_local_L1_limit {n : ℕ} (hn : 0 < n)
    {E : ℕ → Set (Euc n)} {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : MeasurableSet F)
    (hconv : ∀ (c : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall c R)) atTop (𝓝 0)) :
    IsLocallyPerimeterMinimizing F := by
  obtain ⟨C, hC, hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n hn
  refine ⟨hF, ?_, ?_⟩
  · intro c r hr
    exact (perimeter_le_of_eventually_le_of_local_L1 (fun i ↦ (hE i).1) hF hconv
      (Eventually.of_forall fun i ↦ hgrowth (E i) (hE i) c r hr)).trans_lt ENNReal.ofReal_lt_top
  · intro c R hR G hG hcG hsG
    rw [perimeter_eq_iSup_tests]
    refine iSup_le fun V ↦ iSup_le fun hV ↦ ?_
    obtain ⟨a₀, ha₀, hsub⟩ := exists_lt_subset_ball
      ((isClosed_tsupport V).union isClosed_closure) (union_subset hV.2.2.1 hsG)
    let a := max a₀ (R/2)
    have ha : 0 < a := (half_pos hR).trans_le (le_max_right _ _)
    have haR : a < R := max_lt ha₀ (by linarith)
    have hasub : tsupport V ∪ closure (symmDiff F G) ⊆ Metric.ball c a :=
      hsub.trans (Metric.ball_subset_ball (le_max_left _ _))
    let B := (a+R)/2
    have haB : a < B := by dsimp [B]; linarith
    have hBR : B < R := by dsimp [B]; linarith
    have hB : 0 < B := ha.trans haB
    have hann : Tendsto (fun i ↦ volume.real (symmDiff (E i) G ∩
        (Metric.closedBall c B \ Metric.closedBall c a))) atTop (𝓝 0) := by
      apply squeeze_zero (fun i ↦ ENNReal.toReal_nonneg)
        (fun i ↦ measureReal_mono (s₂ := symmDiff (E i) F ∩ Metric.closedBall c B) ?_
          (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c B).measure_ne_top))
        (hconv c B hB)
      intro x hx
      have hxFG : x ∉ symmDiff F G := by
        intro hx'
        exact hx.2.2 (Metric.ball_subset_closedBall
          (hasub (Or.inr (subset_closure hx'))))
      refine ⟨?_, hx.2.1⟩
      simp only [mem_symmDiff] at hxFG ⊢
      have hh := hx.1
      simp only [mem_symmDiff] at hh
      tauto
    have hle : perimeter F (Metric.ball c a) ≤ perimeter G (Metric.ball c R) := by
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε hfin
      apply perimeter_le_of_eventually_le_of_local_L1 (fun i ↦ (hE i).1) hF hconv
      filter_upwards [eventually_minimizing_perimeter_le_of_annular_L1 hE hG c ha haB hann
        (show 0 < (ε:ℝ) from hε)] with i hi
      rw [ENNReal.ofReal_coe_nnreal] at hi
      exact hi.trans (add_le_add (raw_perimeter_mono_region G
        (Metric.ball_subset_ball hBR.le)) le_rfl)
    have hvle : ENNReal.ofReal (∫ x in F, divergence V x) ≤ perimeter F (Metric.ball c a) := by
      rw [perimeter_eq_iSup_tests]
      exact le_iSup_of_le V (le_iSup_of_le
        (show PerimeterAdmissible (Metric.ball c a) V from
          ⟨hV.1, hV.2.1, subset_union_left.trans hasub, hV.2.2.2⟩) le_rfl)
    exact hvle.trans hle

theorem tendsto_perimeter_ball_right {n : ℕ} {F : Set (Euc n)}
    (hF : IsLocallyPerimeterMinimizing F) (c : Euc n) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R ↦ perimeter F (Metric.ball c R)) (𝓝[>] r)
      (𝓝 (perimeterMeasure F (Metric.closedBall c r))) := by
  have ht := tendsto_measure_biInter_gt
    (μ := perimeterMeasure F) (s := fun R : ℝ ↦ Metric.ball c R) (a := r)
    (fun R hR ↦ measurableSet_ball.nullMeasurableSet)
    (fun R S hR hRS ↦ Metric.ball_subset_ball hRS)
    ⟨r+1, by linarith, by
      rw [perimeterMeasure_open F Metric.isOpen_ball]
      exact (hF.2.1 c (r+1) (by linarith)).ne⟩
  simpa only [Metric.biInter_gt_ball, Function.comp_def,
    perimeterMeasure_open F Metric.isOpen_ball] using ht

theorem tendsto_minimizing_perimeter_ball_of_local_L1 {n : ℕ} (hn : 0 < n)
    {E : ℕ → Set (Euc n)} {F : Set (Euc n)}
    (hE : ∀ i, IsLocallyPerimeterMinimizing (E i)) (hF : MeasurableSet F)
    (hconv : ∀ (c : Euc n) (R : ℝ), 0 < R →
      Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩ Metric.closedBall c R)) atTop (𝓝 0))
    (c : Euc n) {r : ℝ} (hr : 0 < r)
    (hnull : perimeterMeasure F (Metric.sphere c r) = 0) :
    Tendsto (fun i ↦ perimeter (E i) (Metric.ball c r)) atTop
      (𝓝 (perimeter F (Metric.ball c r))) := by
  have hmin := locally_minimizing_of_local_L1_limit hn hE hF hconv
  apply tendsto_order.2
  constructor
  · intro A hA
    rw [perimeter_eq_iSup_tests, lt_iSup_iff] at hA
    obtain ⟨V, hV⟩ := hA
    rw [lt_iSup_iff] at hV
    obtain ⟨hV, hAV⟩ := hV
    have hc := hV.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset V)
    have ht := ENNReal.continuous_ofReal.tendsto _ |>.comp
      (tendsto_setIntegral_of_local_symmDiff (fun i ↦ (hE i).1) hF hconv
        (continuous_divergence hV.1) hc)
    filter_upwards [ht.eventually (lt_mem_nhds hAV)] with i hi
    apply hi.trans_le
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le V (le_iSup_of_le hV le_rfl)
  · intro A hA
    have heq : perimeterMeasure F (Metric.closedBall c r) = perimeter F (Metric.ball c r) := by
      rw [← perimeterMeasure_open F Metric.isOpen_ball]
      apply le_antisymm
      · rw [← Metric.ball_union_sphere]
        exact (measure_union_le _ _).trans (by rw [hnull, add_zero])
      · exact measure_mono Metric.ball_subset_closedBall
    have ht := tendsto_perimeter_ball_right hmin c hr
    rw [heq] at ht
    have hh : ∀ᶠ B in 𝓝[>] r, r < B ∧ perimeter F (Metric.ball c B) < A := by
      filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hA)] with B hB hBA
      exact ⟨hB, hBA⟩
    obtain ⟨B, hBr, hBA⟩ := hh.exists
    obtain ⟨ε, hε, hεA⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hBA
    have hann : Tendsto (fun i ↦ volume.real (symmDiff (E i) F ∩
        (Metric.closedBall c B \ Metric.closedBall c r))) atTop (𝓝 0) := by
      exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
        (fun i ↦ measureReal_mono (inter_subset_inter_right _ sdiff_subset)
          (measure_ne_top_of_subset inter_subset_right (isCompact_closedBall c B).measure_ne_top))
        (hconv c B (hr.trans hBr))
    filter_upwards [eventually_minimizing_perimeter_le_of_annular_L1 hE hF c hr hBr hann
      (show 0 < (ε:ℝ) from hε)] with i hi
    rw [ENNReal.ofReal_coe_nnreal] at hi
    exact hi.trans_lt hεA

end RPISingularHarnack

end

end OAI
