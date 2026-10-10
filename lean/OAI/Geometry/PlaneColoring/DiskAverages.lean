import OAI.Geometry.PlaneColoring.Accumulation

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
def diskLaw (ε : ℝ) : Measure ℂ :=
  (volume (Metric.ball (0:ℂ) ε))⁻¹ • volume.restrict (Metric.ball 0 ε)
lemma diskLaw_absolutelyContinuous (ε : ℝ) : diskLaw ε ≪ volume :=
  (Measure.restrict_le_self (s := Metric.ball (0:ℂ) ε)).absolutelyContinuous.smul_left _
lemma diskLaw_probability {ε : ℝ} (hε : 0<ε) : IsProbabilityMeasure (diskLaw ε) := by
  constructor
  simp only [diskLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 hε).ne'
    ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall (0:ℂ) ε).measure_lt_top).ne
def colorFn {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : ℝ := if c z=i then 1 else 0
lemma colorFn_measurable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k) :
    Measurable (colorFn c i) :=
  measurable_one.piecewise (measurableSet_eq_fun hc measurable_const) measurable_zero
lemma colorFn_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : 0≤colorFn c i z := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_le_one {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : colorFn c i z≤1 := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_integrable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (q : ℂ) : Integrable (fun v => colorFn c i (q+v)) μ := by
  apply Integrable.of_bound ((colorFn_measurable hc i).comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall fun v => by
    change ‖colorFn c i (q+v)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i (q+v))]
    exact colorFn_le_one c i (q+v)
def diskAverage {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) : ℝ :=
  ∫ v, colorFn c i (q+v) ∂diskLaw ε
lemma diskAverage_nonneg {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) :
    0≤diskAverage c ε i q := integral_nonneg (fun v => colorFn_nonneg c i (q+v))
lemma diskAverage_le_one {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i : Fin k) (q : ℂ) : diskAverage c ε i q≤1 := by
  have := diskLaw_probability hε
  simpa only [diskAverage,integral_const,probReal_univ,one_smul] using integral_mono (colorFn_integrable (μ := diskLaw ε) hc i q) (integrable_const (1:ℝ))
    (fun v => colorFn_le_one c i (q+v))
lemma diskAverage_sum {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (q : ℂ) : ∑ i,diskAverage c ε i q=1 := by
  have := diskLaw_probability hε
  simp only [diskAverage]
  rw [← integral_finsetSum _ (fun i _ => colorFn_integrable (μ := diskLaw ε) hc i q)]
  simp [colorFn]
lemma colorFn_unit_pair {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {q z : ℂ} (hunit : ‖q-z‖=1) (i : Fin k) :
    ∀ᵐ v ∂(volume : Measure ℂ), colorFn c i (q+v)+colorFn c i (z+v)≤1 := by
  obtain ⟨t,ht⟩ := direction_exists (u := z-q) (by simpa only [norm_sub_rev] using hunit)
  have ha := (measurePreserving_add_left (volume : Measure ℂ) q).quasiMeasurePreserving.ae
    (weak_all_directions c hc hw t)
  filter_upwards [ha] with v hv
  have hne : c (q+v)≠c (z+v) := by
    convert hv using 1
    rw [ht]
    congr 1
    ring
  simp only [colorFn]
  split_ifs with h1 h2 h2 <;> try norm_num
  exact False.elim (hne (h1.trans h2.symm))
lemma diskAverage_unit_pair {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {ε : ℝ} (hε : 0<ε) {q z : ℂ} (hunit : ‖q-z‖=1) (i : Fin k) :
    diskAverage c ε i q+diskAverage c ε i z≤1 := by
  have := diskLaw_probability hε
  rw [diskAverage,diskAverage,← integral_add (colorFn_integrable (μ := diskLaw ε) hc i q) (colorFn_integrable (μ := diskLaw ε) hc i z)]
  simpa using integral_mono_ae ((colorFn_integrable (μ := diskLaw ε) hc i q).add (colorFn_integrable (μ := diskLaw ε) hc i z))
    (integrable_const (1:ℝ)) ((diskLaw_absolutelyContinuous ε).ae_le (colorFn_unit_pair hc hw hunit i))
end EuclideanFiveColor
end

noncomputable section
open scoped Classical symmDiff
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma volumeReal_ball (q : ℂ) {ε : ℝ} (hε : 0≤ε) : volume.real (Metric.ball q ε)=Real.pi*ε^2 := by
  simp [Measure.real,Complex.volume_ball,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hε,mul_comm]
lemma diskAverage_area {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (ε : ℝ)
    (i : Fin k) (q : ℂ) : diskAverage c ε i q=
      volume.real (Metric.ball q ε ∩ {z | c z=i})/volume.real (Metric.ball (0:ℂ) ε) := by
  have he : (fun v : ℂ => q+v) ⁻¹' Metric.ball q ε = Metric.ball 0 ε := by
    ext v
    simp [Metric.mem_ball,dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure ℂ) q).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft q).measurableEmbedding (colorFn c i) (Metric.ball q ε)
  rw [he] at hi
  unfold diskAverage diskLaw
  rw [integral_smul_measure,ENNReal.toReal_inv,hi]
  have hid : colorFn c i=({z | c z=i} : Set ℂ).indicator (fun _ => (1:ℝ)) := by
    funext v
    simp [colorFn,Set.indicator]
  rw [hid]
  rw [setIntegral_indicator (measurableSet_eq_fun hc measurable_const)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,div_eq_mul_inv]
  ring
lemma ball_ne_top (q : ℂ) (r : ℝ) : volume (Metric.ball q r) ≠ ⊤ :=
  ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall q r).measure_lt_top).ne
lemma symmDiff_balls_subset_annulus (q z : ℂ) (ε : ℝ) :
    Metric.ball q ε ∆ Metric.ball z ε ⊆
      Metric.ball q (ε+dist q z) \ Metric.ball q (ε-dist q z) := by
  intro v hv
  have h1 := dist_triangle v q z
  have h2 := dist_triangle v z q
  rw [dist_comm z q] at h2
  rcases hv with h|h
  · refine ⟨?_,?_⟩
    · change dist v q < ε+dist q z
      exact lt_of_lt_of_le (show dist v q<ε from h.1) (by linarith [dist_nonneg (x := q) (y := z)])
    · intro hh
      have hz : ε≤dist v z := not_lt.mp h.2
      have hh' : dist v q<ε-dist q z := hh
      linarith
  · refine ⟨?_,?_⟩
    · exact lt_of_le_of_lt h2 (by have hh : dist v z<ε := h.1; linarith)
    · intro hh
      have hz : ε≤dist v q := not_lt.mp h.2
      have hh' : dist v q<ε-dist q z := hh
      linarith [dist_nonneg (x := q) (y := z)]
lemma measure_inter_ball_difference (A : Set ℂ) (hA : MeasurableSet A) (q z : ℂ)
    {ε : ℝ} (hd : dist q z≤ε) :
    |volume.real (Metric.ball q ε ∩ A)-volume.real (Metric.ball z ε ∩ A)|≤
      4*Real.pi*ε*dist q z := by
  have hsub : (Metric.ball q ε ∩ A) ∆ (Metric.ball z ε ∩ A) ⊆
      Metric.ball q ε ∆ Metric.ball z ε := by
    intro v hv
    rcases hv with h|h
    · exact Or.inl ⟨h.1.1,fun hvz => h.2 ⟨hvz,h.1.2⟩⟩
    · exact Or.inr ⟨h.1.1,fun hvz => h.2 ⟨hvz,h.1.2⟩⟩
  have hi := abs_measureReal_sub_le_measureReal_symmDiff' (Metric.isOpen_ball.measurableSet.inter hA).nullMeasurableSet
    (Metric.isOpen_ball.measurableSet.inter hA).nullMeasurableSet
    (measure_ne_top_of_subset inter_subset_left (ball_ne_top q ε))
    (measure_ne_top_of_subset inter_subset_left (ball_ne_top z ε))
  have hm := measureReal_mono (hsub.trans (symmDiff_balls_subset_annulus q z ε))
    (measure_ne_top_of_subset sdiff_subset (ball_ne_top q (ε+dist q z)))
  apply hi.trans (hm.trans_eq ?_)
  rw [measureReal_sdiff (Metric.ball_subset_ball (by linarith [dist_nonneg (x := q) (y := z)]))
    measurableSet_ball (ball_ne_top q (ε+dist q z)),volumeReal_ball q (by linarith [dist_nonneg (x := q) (y := z)]),
    volumeReal_ball q (sub_nonneg.mpr hd)]
  ring
lemma diskAverage_lipschitz {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (i : Fin k) : LipschitzWith ⟨4/ε,by positivity⟩ (diskAverage c ε i) := by
  apply LipschitzWith.of_dist_le_mul
  intro q z
  change |diskAverage c ε i q-diskAverage c ε i z|≤(4/ε)*dist q z
  by_cases hd : dist q z≤ε
  · rw [diskAverage_area hc,diskAverage_area hc,← sub_div,abs_div,
      volumeReal_ball 0 hε.le,abs_of_pos (by positivity : 0<Real.pi*ε^2)]
    apply (div_le_iff₀ (by positivity : 0<Real.pi*ε^2)).mpr
    have hh := measure_inter_ball_difference {v | c v=i} (measurableSet_eq_fun hc measurable_const) q z hd
    apply hh.trans_eq
    field_simp
  · have hb : |diskAverage c ε i q-diskAverage c ε i z|≤1 := by
      rw [abs_le]
      constructor <;> linarith [diskAverage_nonneg c ε i q,diskAverage_nonneg c ε i z,
        diskAverage_le_one hc hε i q,diskAverage_le_one hc hε i z]
    apply hb.trans
    rw [div_mul_eq_mul_div,le_div_iff₀ hε]
    linarith [not_le.mp hd]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma colorFn_norm_le_one (i : Fin k) (z : ℂ) : ‖colorFn c i z‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i z)]
  exact colorFn_le_one c i z
lemma diskAverage_product {ε : ℝ} (hε : 0<ε) (i j : Fin k) (q : ℂ) :
    diskAverage c ε i q*diskAverage c ε j q =
      ∫ (h : ℂ × ℂ), colorFn c i (q+h.1)*colorFn c j (q+h.2) ∂(diskLaw ε).prod (diskLaw ε) := by
  have := diskLaw_probability hε
  exact (integral_prod_mul _ _).symm
lemma disk_overlap_swap (hc : Measurable c) {ε : ℝ} (hε : 0<ε) (i j : Fin k) (x : ℂ) (r : ℝ) :
    (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q) =
      ∫ (h : ℂ × ℂ), (∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2))
        ∂(diskLaw ε).prod (diskLaw ε) := by
  have := diskLaw_probability hε
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (ball_ne_top x r).lt_top⟩
  simp_rw [diskAverage_product hε]
  apply integral_integral_swap
  apply Integrable.of_bound
    (((colorFn_measurable hc i).comp (measurable_fst.add measurable_snd.fst)).mul
      ((colorFn_measurable hc j).comp (measurable_fst.add measurable_snd.snd))).aestronglyMeasurable 1
  exact Eventually.of_forall fun z => by
    change ‖colorFn c i _*colorFn c j _‖≤1
    rw [norm_mul]
    exact (mul_le_mul (colorFn_norm_le_one i _) (colorFn_norm_le_one j _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
lemma root_overlap_bound (hc : Measurable c) (i j : Fin k) (x : ℂ) (r R : ℝ) (h₁ h₂ : ℂ)
    (hr : r+‖h₁‖≤R) :
    (∫ q in Metric.ball x r, colorFn c i (q+h₁)*colorFn c j (q+h₂))≤
      volume.real (transitionSet c i j x R (h₂-h₁)) := by
  let T := transitionSet c i j x R (h₂-h₁)
  have hT : MeasurableSet T := transitionSet_measurable c hc i j x R (h₂-h₁)
  have hTf : volume T≠⊤ := (transitionSet_finite c i j x R (h₂-h₁)).ne
  have hI : Integrable (fun q : ℂ => T.indicator (fun _ => (1:ℝ)) (q+h₁)) volume := by
    exact ((integrable_indicator_iff hT).mpr (integrableOn_const (C := (1:ℝ)) hTf)).comp_add_right h₁
  have : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (ball_ne_top x r).lt_top⟩
  have hF : Integrable (fun q : ℂ => colorFn c i (q+h₁)*colorFn c j (q+h₂))
      (volume.restrict (Metric.ball x r)) := by
    apply Integrable.of_bound (((colorFn_measurable hc i).comp (measurable_id.add_const h₁)).mul
      ((colorFn_measurable hc j).comp (measurable_id.add_const h₂))).aestronglyMeasurable 1
    exact Eventually.of_forall fun q => by
      change ‖colorFn c i (q+h₁)*colorFn c j (q+h₂)‖≤1
      rw [norm_mul]
      simpa using mul_le_mul (colorFn_norm_le_one i (q+h₁)) (colorFn_norm_le_one j (q+h₂)) (norm_nonneg _) zero_le_one
  have hle : (∫ q in Metric.ball x r, colorFn c i (q+h₁)*colorFn c j (q+h₂))≤
      ∫ q in Metric.ball x r, T.indicator (fun _ => (1:ℝ)) (q+h₁) := by
    apply integral_mono_ae hF hI.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
    by_cases h1 : c (q+h₁)=i
    · by_cases h2 : c (q+h₂)=j
      · have hmem : q+h₁∈T := by
          refine ⟨?_,Or.inl ⟨h1,?_⟩⟩
          · change dist (q+h₁) x<R
            have he : q+h₁-x=(q-x)+h₁ := by ring
            rw [dist_eq_norm,he]
            have hq' : ‖q-x‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
            exact (norm_add_le _ _).trans_lt (by linarith)
          · convert h2 using 1; congr 1; ring
        simp [colorFn,h1,h2,Set.indicator_of_mem hmem]
      · simp only [colorFn,ite_eq_left h1,ite_eq_right h2,mul_zero]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · simp only [colorFn,ite_eq_right h1,zero_mul]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  apply hle.trans
  calc
    (∫ q in Metric.ball x r, T.indicator (fun _ => (1:ℝ)) (q+h₁)) ≤
      ∫ q, T.indicator (fun _ => (1:ℝ)) (q+h₁) :=
        integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun q => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hI
    _ = volume.real T := by
      rw [(measurePreserving_add_right volume h₁).integral_comp
        (MeasurableEquiv.addRight h₁).measurableEmbedding]
      rw [integral_indicator hT]
      simp
lemma root_overlap_zero (i j : Fin k) (hne : i≠j) (x : ℂ) (r : ℝ) (h : ℂ) :
    (∫ q in Metric.ball x r, colorFn c i (q+h)*colorFn c j (q+h))=0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun q => by
    simp only [colorFn]
    split_ifs with hi hj hj <;> try norm_num
    exact False.elim (hne (hi.symm.trans hj))
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
variable {k : ℕ} {c : ℂ → Fin k}
lemma missing_edge_uniform {i j : Fin k} (hne : i≠j) {x : ℂ} {R : ℝ}
    (ht : Tendsto (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) (𝓝 0))
    {η : ℝ} (hη : 0<η) : ∃ δ>0, ∀ h : ℂ, ‖h‖<δ →
      volume.real (transitionSet c i j x R h)≤η*‖h‖ := by
  have hev : ∀ᶠ h in 𝓝[≠] (0:ℂ), transitionRatio c i j x R h<ENNReal.ofReal η :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨δ,hδ,fun h hh => ?_⟩
  by_cases hz : h=0
  · subst h
    have he : transitionSet c i j x R 0=∅ := by
      ext q
      simp only [transitionSet,mem_ofPred_eq,add_zero,mem_empty_iff_false,iff_false]
      rintro ⟨_,hh|hh⟩
      · exact hne (hh.1.symm.trans hh.2)
      · exact hne (hh.2.symm.trans hh.1)
    simp [he]
  · have hr : transitionRatio c i j x R h ≤ ENNReal.ofReal η :=
      le_of_lt (hd ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hh,hz⟩)
    have hm := (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)).ne'
      ENNReal.ofReal_ne_top).mp hr
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hm
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofReal hη.le,ENNReal.toReal_ofReal (norm_nonneg h)] using hreal
lemma diskLaw_mem_ball {ε : ℝ} (_hε : 0<ε) : ∀ᵐ h ∂diskLaw ε, h∈Metric.ball (0:ℂ) ε := by
  rw [diskLaw,Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (ball_ne_top 0 ε))]
  exact ae_restrict_mem measurableSet_ball
lemma disk_overlap_bound (hc : Measurable c) {i j : Fin k} (hne : i≠j)
    (x : ℂ) (r R : ℝ) {ε δ η : ℝ} (hε : 0<ε) (hη : 0≤η)
    (hr : r+ε≤R) (hδ : 2*ε≤δ)
    (hd : ∀ h : ℂ, ‖h‖<δ → volume.real (transitionSet c i j x R h)≤η*‖h‖) :
    (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)≤2*η*ε := by
  have := diskLaw_probability hε
  rw [disk_overlap_swap hc hε]
  have hab : ∀ᵐ h ∂(diskLaw ε).prod (diskLaw ε), h.1∈Metric.ball (0:ℂ) ε ∧ h.2∈Metric.ball (0:ℂ) ε := by
    apply (ae_prod_iff_ae_ae (measurableSet_ball.prod measurableSet_ball)).mpr
    filter_upwards [diskLaw_mem_ball hε] with h₁ hh₁
    filter_upwards [diskLaw_mem_ball hε] with h₂ hh₂
    exact ⟨hh₁,hh₂⟩
  have hh : ∀ᵐ h ∂(diskLaw ε).prod (diskLaw ε),
      (∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2))≤2*η*ε := by
    filter_upwards [hab] with h hh
    have ha : ‖h.1‖<ε := by simpa only [Metric.mem_ball,dist_zero_right] using hh.1
    have hb : ‖h.2‖<ε := by simpa only [Metric.mem_ball,dist_zero_right] using hh.2
    by_cases he : h.1=h.2
    · rw [he,root_overlap_zero i j hne]
      positivity
    · have hn : ‖h.2-h.1‖ < 2*ε := (norm_sub_le _ _).trans_lt (by linarith)
      apply (root_overlap_bound hc i j x r R h.1 h.2 (by linarith)).trans
      apply (hd _ (hn.trans_le hδ)).trans
      nlinarith
  have hn : 0≤ᵐ[(diskLaw ε).prod (diskLaw ε)]
      fun h => ∫ q in Metric.ball x r, colorFn c i (q+h.1)*colorFn c j (q+h.2) :=
    Eventually.of_forall fun h => integral_nonneg fun q => mul_nonneg (colorFn_nonneg c i _) (colorFn_nonneg c j _)
  simpa using integral_mono_of_nonneg hn (integrable_const (2*η*ε)) hh
lemma missing_edge_overlap (hc : Measurable c) {i j : Fin k} (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0, ∀ r<R,
      Tendsto (fun ε : ℝ => (∫ q in Metric.ball x r, diskAverage c ε i q*diskAverage c ε j q)/ε)
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R,hR,ht⟩ := missing_edge_lim c i j hne he
  refine ⟨R,hR,fun r hr => ?_⟩
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (div_nonneg (integral_nonneg fun q => mul_nonneg (diskAverage_nonneg c ε i q)
      (diskAverage_nonneg c ε j q)) (le_of_lt hε))
  · intro b hb
    obtain ⟨δ,hδ,hd⟩ := missing_edge_uniform hne ht (show 0<b/4 by linarith)
    have hv : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min (R-r) (δ/2) :=
      (eventually_lt_nhds (lt_min (by linarith) (by linarith))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hv] with ε hε hv
    have hh := disk_overlap_bound hc hne x r R (show 0<ε from hε) (show 0≤b/4 by linarith)
      (by have := (lt_min_iff.mp hv).1; linarith) (by have := (lt_min_iff.mp hv).2; linarith) hd
    apply (div_le_div_of_nonneg_right hh (le_of_lt hε)).trans_lt
    have hz : ε≠0 := ne_of_gt hε
    field_simp
    linarith
end EuclideanFiveColor
end

end OAI
