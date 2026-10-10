import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.ProjectionMoments

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

noncomputable def smoothingWidth (j : ℕ) : ℝ := 1 / ((j:ℝ)+1)

lemma smoothingWidth_pos (j : ℕ) : 0 < smoothingWidth j := by
  unfold smoothingWidth
  positivity

lemma smoothingWidth_tendsto : Tendsto smoothingWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def boxAverage {T : Type*} {k : ℕ} (η : ℝ)
    (g : T × (Fin k → ℝ) → ℝ≥0∞) (p : T × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ u, boxKernel η p.2 u * g (p.1,u)

lemma measurable_boxAverage {T : Type*} [MeasurableSpace T] {k : ℕ}
    (η : ℝ) (g : T × (Fin k → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    Measurable (boxAverage η g) := by
  have h : Measurable (fun p : (T × (Fin k → ℝ)) × (Fin k → ℝ) =>
      boxKernel η p.1.2 p.2 * g (p.1.1,p.2)) :=
    ((measurable_boxKernel η).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact h.lintegral_prod_right

lemma open_box_eventually {T : Type*} [PseudoMetricSpace T] {k : ℕ}
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) (p : T × (Fin k → ℝ))
    (hp : p ∈ O) : ∀ᶠ j in atTop, ∀ u ∈ closedBox p.2 (smoothingWidth j), (p.1,u) ∈ O := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hp)
  filter_upwards [smoothingWidth_tendsto.eventually (gt_mem_nhds hε)] with j hj
  intro u hu
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  apply max_lt
  · simpa using hε
  · apply lt_of_le_of_lt _ hj
    apply (dist_pi_le_iff (smoothingWidth_pos j).le).mpr
    intro i
    simpa only [Real.dist_eq] using hu i

lemma indicator_le_liminf_boxAverage {T : Type*} [PseudoMetricSpace T] {k : ℕ}
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) (p : T × (Fin k → ℝ)) :
    O.indicator (fun _ => (1:ℝ≥0∞)) p ≤
      liminf (fun j : ℕ => boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) p) atTop := by
  classical
  by_cases hp : p ∈ O
  · rw [Set.indicator_of_mem hp]
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [open_box_eventually O hO p hp] with j hj
    have he : boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) p = 1 := by
      calc
        _ = ∫⁻ u, boxKernel (smoothingWidth j) p.2 u := by
          apply lintegral_congr
          intro u
          by_cases hu : u ∈ closedBox p.2 (smoothingWidth j)
          · rw [Set.indicator_of_mem (hj u hu), mul_one]
          · rw [boxKernel, Set.indicator_of_notMem hu, zero_mul]
        _ = 1 := lintegral_boxKernel _ (smoothingWidth_pos j) _
    exact he.ge
  · rw [Set.indicator_of_notMem hp]
    exact zero_le

noncomputable def mixtureDensity {T E : Type*} [MeasurableSpace E] {k : ℕ}
    (μ : Measure E) (b : T × E → Fin k → ℝ) (η : ℝ) (p : T × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, boxKernel η (b (p.1,z)) p.2 ∂μ

lemma measurable_mixture_kernel {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ) :
    Measurable (fun p : (T × (Fin k → ℝ)) × E => boxKernel η (b (p.1.1,p.2)) p.1.2) :=
  (measurable_boxKernel η).comp
    ((hb.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))

lemma measurable_mixtureDensity {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (μ : Measure E) [SFinite μ] (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ) :
    Measurable (mixtureDensity μ b η) := (measurable_mixture_kernel b hb η).lintegral_prod_right

lemma lintegral_mixtureDensity_mul {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (η : ℝ)
    (g : T × (Fin k → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p, mixtureDensity μ b η p * g p ∂σ.prod volume) =
      ∫⁻ q : T × E, boxAverage η g (q.1,b q) ∂σ.prod μ := by
  rw [lintegral_prod (μ := σ) (ν := volume)
      (fun p => mixtureDensity μ b η p * g p) (by
        exact ((measurable_mixtureDensity μ b hb η).mul hg).aemeasurable),
    lintegral_prod (μ := σ) (ν := μ) (fun q => boxAverage η g (q.1,b q)) (by
      exact ((measurable_boxAverage η g hg).comp (measurable_fst.prodMk hb)).aemeasurable)]
  apply lintegral_congr
  intro x
  have h : Measurable (fun p : (Fin k → ℝ) × E =>
      boxKernel η (b (x,p.2)) p.1 * g (x,p.1)) :=
    ((measurable_boxKernel η).comp
      ((hb.comp (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)).mul
      (hg.comp (measurable_const.prodMk measurable_fst))
  calc
    _ = ∫⁻ u, ∫⁻ z, boxKernel η (b (x,z)) u * g (x,u) ∂μ := by
      apply lintegral_congr
      intro u
      exact (lintegral_mul_const (g (x,u)) ((measurable_boxKernel η).comp
        ((hb.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const))).symm
    _ = _ := lintegral_lintegral_swap h.aemeasurable

lemma measure_rpow_bound_of_open {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (ν ρ : Measure E) [ρ.OuterRegular] (K : ℝ≥0∞) (hK : K ≠ ∞)
    (r : ℝ) (hr : 0 ≤ r)
    (hopen : ∀ O : Set E, IsOpen O → ν O ≤ K*(ρ O)^r) (S : Set E) :
    ν S ≤ K*(ρ S)^r := by
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun j : ℕ => K*(ρ S+ENNReal.ofReal (1 / ((j:ℝ)+1)))^r)
      atTop (𝓝 (K*(ρ S)^r)) := by
    apply ENNReal.Tendsto.const_mul _ (Or.inr hK)
    simpa using ((tendsto_const_nhds.add ht).ennrpow_const r)
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have he : ENNReal.ofReal (1/((j:ℝ)+1)) ≠ 0 := by positivity
  obtain ⟨O,hSO,hO,hρO⟩ := S.exists_isOpen_le_add ρ he
  exact (measure_mono hSO).trans ((hopen O hO).trans
    (mul_le_mul_right (ENNReal.rpow_le_rpow hρO hr) _))

lemma lintegral_holder_set_bound {E : Type*} [MeasurableSpace E]
    (ρ : Measure E) (F : E → ℝ≥0∞) (hF : Measurable F)
    {m : ℕ} (hm : 1 < m) (K : ℝ≥0∞)
    (hmoment : (∫⁻ p, F p ^ m ∂ρ) ≤ K)
    (S : Set E) (hS : MeasurableSet S) :
    (∫⁻ p in S, F p ∂ρ) ≤ K^(1/(m:ℝ))*(ρ S)^(1-1/(m:ℝ)) := by
  have hm' : (1:ℝ) < m := by exact_mod_cast hm
  have hconj : (m:ℝ).HolderConjugate ((m:ℝ)/(m-1)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hm', ?_⟩
    field_simp
    ring
  have he : 1/((m:ℝ)/(m-1)) = 1-1/(m:ℝ) := by field_simp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hconj hF.aemeasurable
    ((measurable_const.indicator hS).aemeasurable :
      AEMeasurable (S.indicator (fun _ => (1:ℝ≥0∞))) ρ)
  have hleft : (∫⁻ x, (F * S.indicator (fun _ => (1:ℝ≥0∞))) x ∂ρ) = ∫⁻ x in S, F x ∂ρ := by
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  have hright : (∫⁻ x, (S.indicator (fun _ => (1:ℝ≥0∞)) x)^((m:ℝ)/(m-1)) ∂ρ) = ρ S := by
    have hpos : 0 < (m:ℝ)/(m-1) := by positivity
    rw [← lintegral_indicator_one hS]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ S <;> simp [hx, hpos]
  rw [hleft, hright, he] at h
  simp only [ENNReal.rpow_natCast] at h
  exact h.trans (mul_le_mul_left (ENNReal.rpow_le_rpow hmoment (by positivity)) _)

lemma bounded_layer_cake {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (g : E → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂ν) = ∫⁻ t in Ioo (0:ℝ) 1, ν {x | t < g x} := by
  rw [lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall hg0) hg.aemeasurable,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < 1
    · simp [ht0, ht1]
    · have hz : {x | t < g x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact not_lt.mpr ((hg1 x).trans (le_of_not_gt ht1))
      simp [ht0, ht1, hz]
  · simp [ht0]

lemma bounded_borel_test_of_measure_rpow_bound {E : Type*} [MeasurableSpace E]
    (ν ρ : Measure E) (K : ℝ≥0∞) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbound : ∀ S : Set E, MeasurableSet S → ν S ≤ K*(ρ S)^r)
    (g : E → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≤ K*(∫⁻ x, ENNReal.ofReal (g x) ∂ρ)^r := by
  have ht : Measurable (fun t : ℝ => ρ {x | t < g x}) := by
    apply Antitone.measurable
    intro s t hst
    exact measure_mono (fun x hx => lt_of_le_of_lt hst hx)
  rw [bounded_layer_cake ν g hg hg0 hg1, bounded_layer_cake ρ g hg hg0 hg1]
  calc
    _ ≤ ∫⁻ t in Ioo (0:ℝ) 1, K*(ρ {x | t < g x})^r := by
      apply lintegral_mono
      intro t
      exact hbound _ (measurableSet_lt measurable_const hg)
    _ = K * ∫⁻ t in Ioo (0:ℝ) 1, (ρ {x | t < g x})^r :=
      lintegral_const_mul _ (ht.pow_const r)
    _ ≤ K * ((∫⁻ t in Ioo (0:ℝ) 1, ρ {x | t < g x})^r *
        (∫⁻ t in Ioo (0:ℝ) 1, (1:ℝ≥0∞))^(1-r)) := by
      apply mul_le_mul_right
      simpa only [ENNReal.one_rpow, mul_one] using
        ENNReal.lintegral_mul_norm_pow_le (μ := volume.restrict (Ioo (0:ℝ) 1))
          (g := fun _ : ℝ => (1:ℝ≥0∞))
          ht.aemeasurable aemeasurable_const hr0 (sub_nonneg.mpr hr1) (by ring : r+(1-r)=1)
    _ = _ := by simp

noncomputable def exactMixtureLaw {T E : Type*} [MeasurableSpace T] [MeasurableSpace E]
    {k : ℕ} (σ : Measure T) (μ : Measure E) (b : T × E → Fin k → ℝ) :
    Measure (T × (Fin k → ℝ)) := (σ.prod μ).map (fun q => (q.1,b q))

lemma exactMixtureLaw_open_bound {T E : Type*} [PseudoMetricSpace T]
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace E] {k m : ℕ}
    (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (hm : 1 < m) (K : ℝ≥0∞)
    (hK : ∀ η : ℝ, 0 < η →
      (∫⁻ p, mixtureDensity μ b η p ^ m ∂σ.prod volume) ≤ K)
    (O : Set (T × (Fin k → ℝ))) (hO : IsOpen O) :
    exactMixtureLaw σ μ b O ≤ K^(1/(m:ℝ))*((σ.prod volume) O)^(1-1/(m:ℝ)) := by
  have hmap : Measurable (fun q : T × E => (q.1,b q)) := measurable_fst.prodMk hb
  have hg : Measurable (O.indicator (fun _ => (1:ℝ≥0∞))) :=
    measurable_const.indicator hO.measurableSet
  have havg (j : ℕ) : Measurable (fun q : T × E =>
      boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q)) :=
    (measurable_boxAverage _ _ hg).comp hmap
  calc
    _ = ∫⁻ q : T × E, O.indicator (fun _ => (1:ℝ≥0∞)) (q.1,b q) ∂σ.prod μ := by
      rw [← lintegral_indicator_one hO.measurableSet, exactMixtureLaw]
      exact lintegral_map hg hmap
    _ ≤ ∫⁻ q : T × E, liminf (fun j : ℕ =>
        boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q)) atTop ∂σ.prod μ := by
      exact lintegral_mono (fun q => indicator_le_liminf_boxAverage O hO _)
    _ ≤ liminf (fun j : ℕ => ∫⁻ q : T × E,
        boxAverage (smoothingWidth j) (O.indicator (fun _ => 1)) (q.1,b q) ∂σ.prod μ) atTop :=
      lintegral_liminf_le havg
    _ ≤ _ := by
      refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
      apply Filter.Eventually.frequently
      apply Eventually.of_forall
      intro j
      rw [← lintegral_mixtureDensity_mul σ μ b hb _ _ hg]
      have he : (∫⁻ p, mixtureDensity μ b (smoothingWidth j) p *
          O.indicator (fun _ => (1:ℝ≥0∞)) p ∂σ.prod volume) =
          ∫⁻ p in O, mixtureDensity μ b (smoothingWidth j) p ∂σ.prod volume := by
        rw [← lintegral_indicator hO.measurableSet]
        apply lintegral_congr
        intro p
        by_cases hp : p ∈ O <;> simp [hp]
      rw [he]
      exact lintegral_holder_set_bound _ _ (measurable_mixtureDensity μ b hb _) hm K
        (hK _ (smoothingWidth_pos j)) O hO.measurableSet

lemma exactMixtureLaw_borel_test {T E : Type*} [PseudoMetricSpace T]
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace E] {k m : ℕ}
    (σ : Measure T) [SFinite σ] (μ : Measure E) [SFinite μ]
    [(σ.prod (volume : Measure (Fin k → ℝ))).OuterRegular]
    (b : T × E → Fin k → ℝ) (hb : Measurable b) (hm : 1 < m)
    (K : ℝ≥0∞) (hKfinite : K ≠ ∞)
    (hK : ∀ η : ℝ, 0 < η → (∫⁻ p, mixtureDensity μ b η p ^ m ∂σ.prod volume) ≤ K)
    (g : T × (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    (∫⁻ p, ENNReal.ofReal (g p) ∂exactMixtureLaw σ μ b) ≤
      K^(1/(m:ℝ))*(∫⁻ p, ENNReal.ofReal (g p) ∂σ.prod volume)^(1-1/(m:ℝ)) := by
  have hm' : (1:ℝ) < m := by exact_mod_cast hm
  have hr : 0 ≤ 1-1/(m:ℝ) := by
    rw [sub_nonneg]
    exact (div_le_one (by positivity)).mpr hm'.le
  apply bounded_borel_test_of_measure_rpow_bound _ _ _ _ hr (by exact sub_le_self _ (by positivity)) _ g hg hg0 hg1
  intro S hS
  exact measure_rpow_bound_of_open _ _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKfinite)
    _ hr (exactMixtureLaw_open_bound σ μ b hb hm K hK) S

end RepeatedLocalization

end OAI
