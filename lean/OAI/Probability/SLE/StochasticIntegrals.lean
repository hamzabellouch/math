import Mathlib
import OAI.Probability.SLE.SpatialMeans

namespace OAI

/-! Stochastic Integrals for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
namespace SLEExactGauge
noncomputable def spatialLaterKernel (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (r : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  if spatialHitTime γ z r = ⊤ then 0 else
    let s := (spatialHitTime γ z r).untopD 0
    if z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s ∧
        spatialHitTime γ w r ≤ s then ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) else 0

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.spatial_later_kernel_integral
    (h : IsCapacityTwoWitness U γ G F) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫⁻ w, spatialLaterKernel γ G r z w) ≤ ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  classical
  by_cases ht : spatialHitTime γ z r = ⊤
  · simp only [spatialLaterKernel, ite_eq_left ht, lintegral_zero, zero_le]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
  by_cases hz : z ∈ survivingDomain γ s
  · let L := {w | w ∈ survivingDomain γ s ∧ infDist w (frontier (survivingDomain γ s)) ≤ r}
    have hp (w : ℂ) : spatialLaterKernel γ G r z w ≤
        L.indicator (fun w => ENNReal.ofReal (halfPlaneGreen (G s z) (G s w))) w := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe]
      by_cases ha : z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s ∧ spatialHitTime γ w r ≤ s
      · rw [ite_eq_left ha]
        obtain ⟨v, hv, he⟩ := (spatialHitTime_le_iff h.1 w r s).mp ha.2.2
        have hw : w ∈ L := ⟨ha.2.1, (surviving_frontier_distance_le_past s v hv.2 w ha.2.1).trans_eq he⟩
        rw [Set.indicator_of_mem hw]
      · rw [ite_eq_right ha]
        exact zero_le
    calc
      _ ≤ ∫⁻ w, L.indicator (fun w => ENNReal.ofReal (halfPlaneGreen (G s z) (G s w))) w :=
        lintegral_mono hp
      _ ≤ ∫⁻ w in L, ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) := lintegral_indicator_le _ _
      _ ≤ _ := h.boundary_layer_green s hr hz
  · have he (w : ℂ) : spatialLaterKernel γ G r z w = 0 := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe]
      simp only [hz, false_and, ite_false]
    simp only [he, lintegral_zero, zero_le]

lemma slab_product_zero_of_not_live_at_start
    (κ r ε : ℝ) (z w : ℂ) (s : ℝ≥0) (hs : spatialHitTime γ z r = s)
    (hn : ¬ (z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s)) (t : ℝ≥0) :
    spatialSlabCoefficient κ U γ G r ε t z * spatialSlabCoefficient κ U γ G r ε t w = 0 := by
  by_cases ha : spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t
  · by_cases hb : spatialHitTime γ w r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ w ε ∧
        w ∈ survivingDomain γ t
    · have hst : s ≤ t := WithTop.coe_le_coe.mp (hs ▸ ha.1)
      exact (hn ⟨survivingDomain_antitone γ hst ha.2.2, survivingDomain_antitone γ hst hb.2.2⟩).elim
    · simp only [spatialSlabCoefficient, ite_eq_right hb, mul_zero]
  · simp only [spatialSlabCoefficient, ite_eq_right ha, zero_mul]

lemma IsCapacityTwoWitness.slab_pair_ordered
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w)
    (horder : spatialHitTime γ w r ≤ spatialHitTime γ z r) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        spatialLaterKernel γ G r z w := by
  classical
  by_cases ht : spatialHitTime γ z r = ⊤
  · have he (t : ℝ) : spatialSlabCoefficient κ U γ G r ε t.toNNReal z = 0 := by
      have hn : ¬ (spatialHitTime γ z r ≤ t.toNNReal ∧
          (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧ z ∈ survivingDomain γ t.toNNReal) := by
        intro hh
        rw [ht] at hh
        exact WithTop.coe_ne_top (top_le_iff.mp hh.1)
      exact ite_eq_right hn
    simp only [he, zero_mul, abs_zero, ENNReal.ofReal_zero, lintegral_zero, zero_le]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
  by_cases hl : z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s
  · have hord : spatialHitTime γ w r ≤ s := hs ▸ horder
    have he : spatialLaterKernel γ G r z w = ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe, ite_eq_left ⟨hl.1, hl.2, hord⟩]
    rw [he]
    have hb := h.slab_pair_later_start hU hκ hκ4 hε r z w hzy hwy hne s hs.symm
    convert hb using 1
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (by norm_num))]
    congr 1
    ring
  · simp only [slab_product_zero_of_not_live_at_start κ r ε z w s hs.symm hl,
      abs_zero, ENNReal.ofReal_zero, lintegral_zero, zero_le]

 

lemma IsCapacityTwoWitness.slab_pair_kernel_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (spatialLaterKernel γ G r z w + spatialLaterKernel γ G r w z) := by
  rcases le_total (spatialHitTime γ w r) (spatialHitTime γ z r) with ho | ho
  · exact (h.slab_pair_ordered hU hκ hκ4 hε r z w hzy hwy hne ho).trans
      (mul_le_mul le_rfl (le_add_right le_rfl) bot_le bot_le)
  · have hb := h.slab_pair_ordered hU hκ hκ4 hε r w z hwy hzy hne.symm ho
    simp only [mul_comm (spatialSlabCoefficient κ U γ G r ε _ w)] at hb
    exact hb.trans (mul_le_mul le_rfl (le_add_left le_rfl) bot_le bot_le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma spatialHitTime_measurable_point (hc : Continuous γ) (r : ℝ) :
    Measurable (fun z => spatialHitTime γ z r) := by
  have hm := spatialHitTime_measurable (fun _ : Unit => γ) (fun _ => hc)
    (fun _ => measurable_const) r
  exact hm.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma IsCapacityTwoWitness.joint_live_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) :
    MeasurableSet {p : ℝ≥0 × ℂ | p.2 ∈ survivingDomain γ p.1} := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  have hm := c.live_measurable (fun _ => γ) (fun _ => G) (fun _ => F) (fun _ => hU) (fun _ => h)
  exact hm.preimage (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ()))))

lemma IsCapacityTwoWitness.killed_chart_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) :
    Measurable (fun p : ℝ≥0 × ℂ => if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0) := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  convert c.jointChart_measurable.comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ())))) using 1
  funext p
  exact (c.jointChart_eq () hU h p.1 p.2).symm

lemma IsCapacityTwoWitness.spatial_later_kernel_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (r : ℝ) :
    Measurable (fun p : ℂ × ℂ => spatialLaterKernel γ G r p.1 p.2) := by
  classical
  let H (p : ℝ≥0 × ℂ) := if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0
  let s (z : ℂ) := (spatialHitTime γ z r).untopD 0
  have hm := spatialHitTime_measurable_point h.1 r
  have hs : Measurable s := hm.untopD 0
  have hH : Measurable H := h.killed_chart_measurable hU
  have hz : Measurable (fun p : ℂ × ℂ => H (s p.1, p.1)) := hH.comp ((hs.comp measurable_fst).prodMk measurable_fst)
  have hw : Measurable (fun p : ℂ × ℂ => H (s p.1, p.2)) := hH.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  have hK : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2)))) := by
    exact (Real.measurable_log.comp ((hz.sub (Complex.continuous_conj.measurable.comp hw)).div (hz.sub hw)).norm).ennreal_ofReal
  have hzl : MeasurableSet {p : ℂ × ℂ | p.1 ∈ survivingDomain γ (s p.1)} :=
    (h.joint_live_measurable hU).preimage ((hs.comp measurable_fst).prodMk measurable_fst)
  have hwl : MeasurableSet {p : ℂ × ℂ | p.2 ∈ survivingDomain γ (s p.1)} :=
    (h.joint_live_measurable hU).preimage ((hs.comp measurable_fst).prodMk measurable_snd)
  have ho : MeasurableSet {p : ℂ × ℂ | spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0)} :=
    measurableSet_le (hm.comp measurable_snd) ((hs.comp measurable_fst).withTop_coe)
  have hnf : MeasurableSet {p : ℂ × ℂ | spatialHitTime γ p.1 r = ⊤} :=
    measurableSet_eq_fun (hm.comp measurable_fst) measurable_const
  have hk : Measurable (fun p : ℂ × ℂ =>
      if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then
        ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2))) else 0) := by
    exact @Measurable.ite _ _ _ _ _ _
      (fun p : ℂ × ℂ => p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0)) (fun _ => inferInstance)
      (hzl.inter (hwl.inter ho)) hK (measurable_const (a := (0 : ℝ≥0∞)))
  have hh : Measurable (fun p : ℂ × ℂ => if spatialHitTime γ p.1 r = ⊤ then 0 else
      if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then
        ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2))) else 0) := by
    exact @Measurable.ite _ _ _ _ _ _ (fun p : ℂ × ℂ => spatialHitTime γ p.1 r = ⊤)
      (fun _ => inferInstance) hnf
      (measurable_const (a := (0 : ℝ≥0∞))) hk
  convert hh using 1
  funext p
  dsimp only [spatialLaterKernel]
  by_cases hn : spatialHitTime γ p.1 r = ⊤
  · simp only [hn, ite_eq_left]
  · rw [ite_eq_right hn, ite_eq_right hn]
    change (if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then _ else _) = _
    split_ifs with hl
    · simp only [H, ite_eq_left hl.1, ite_eq_left hl.2.1]
      rfl
    · rfl

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.spatial_later_kernel_double
    (h : IsCapacityTwoWitness U γ G F) {r : ℝ} (hr : 0 < r) (A : Set ℂ) :
    (∫⁻ z in A, ∫⁻ w in A, spatialLaterKernel γ G r z w) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A := by
  calc
    _ ≤ ∫⁻ _z in A, ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
      apply lintegral_mono
      intro z
      exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans (h.spatial_later_kernel_integral hr z)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

lemma sym_pair_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] (K : α → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    (∫⁻ z, ∫⁻ w, C * (K z w + K w z) ∂μ ∂μ) =
      C * (2 * (∫⁻ z, ∫⁻ w, K z w ∂μ ∂μ)) := by
  have hi (z : α) : (∫⁻ w, C * (K z w + K w z) ∂μ) =
      C * ((∫⁻ w, K z w ∂μ) + (∫⁻ w, K w z ∂μ)) := by
    rw [lintegral_const_mul' C _ hC]
    have hm : Measurable (fun w => K z w) := hK.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hm]
  rw [lintegral_congr hi, lintegral_const_mul' C _ hC]
  have ho : Measurable (fun z => ∫⁻ w, K z w ∂μ) := hK.lintegral_prod_right'
  rw [lintegral_add_left ho]
  have hs : (∫⁻ z, ∫⁻ w, K w z ∂μ ∂μ) = (∫⁻ z, ∫⁻ w, K z w ∂μ ∂μ) :=
    lintegral_lintegral_swap (hK.comp measurable_swap).aemeasurable
  rw [hs, two_mul]

lemma IsCapacityTwoWitness.spatial_pair_lintegral_le
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ z in A, ∫⁻ w in A, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
    (∫⁻ z in A, ∫⁻ w in A,
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (spatialLaterKernel γ G r z w + spatialLaterKernel γ G r w z)) := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hA] with z hz
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
  exact h.slab_pair_kernel_bound hU hκ hκ4 hε r z w (hheight z hz) (hheight w hw) hne.symm

 

theorem IsCapacityTwoWitness.spatial_slab_pair_area_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ z in A, ∫⁻ w in A, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  refine (h.spatial_pair_lintegral_le hU hκ hκ4 hε r A hA hheight).trans ?_
  rw [sym_pair_lintegral (volume.restrict A) (spatialLaterKernel γ G r) (h.spatial_later_kernel_measurable hU r)
    _ ENNReal.ofReal_ne_top]
  exact mul_le_mul le_rfl
    (mul_le_mul le_rfl (h.spatial_later_kernel_double hr A) bot_le bot_le) bot_le bot_le

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.killed_green_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ) :
    Measurable (fun p : ℝ≥0 × ℂ => greenDensity κ U γ G p.1 p.2) := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  let B (t : ℝ≥0) (_ : Unit) := U t / Real.sqrt κ
  have hBm : Measurable (fun p : ℝ≥0 × Unit => B p.1 p.2) :=
    (hU.measurable.comp measurable_fst).div_const _
  have hm := (c.jointGreen_measurable κ B hBm).comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ()))))
  convert hm using 1
  funext p
  apply (c.jointGreen_eq κ B () hU _ h p.1 p.2).symm
  intro t
  dsimp only [B]
  field_simp [(Real.sqrt_pos.mpr hκ).ne']

lemma IsCapacityTwoWitness.green_coefficient_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ) :
    Measurable (fun p : ℝ≥0 × ℂ => greenBrownianCoefficient κ U γ G p.1 p.2) := by
  classical
  let H (p : ℝ≥0 × ℂ) := if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0
  have hZ : Measurable (fun p : ℝ≥0 × ℂ => H p - (U p.1 : ℂ)) :=
    (h.killed_chart_measurable hU).sub (Complex.measurable_ofReal.comp (hU.measurable.comp measurable_fst))
  have hb := (((Complex.measurable_re.comp hZ).const_mul (Real.sqrt κ * greenExponent κ)).div
    (hZ.norm.pow_const 2)).mul (h.killed_green_measurable hU hκ)
  convert hb using 1
  funext p
  by_cases hl : p.2 ∈ survivingDomain γ p.1
  · simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, H, ite_eq_left hl, greenBrownianCoefficient]
  · simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, greenBrownianCoefficient, greenDensity, ite_eq_right hl, mul_zero]

lemma IsCapacityTwoWitness.spatial_slab_coefficient_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ)
    (r ε : ℝ) :
    Measurable (fun p : ℝ≥0 × ℂ => spatialSlabCoefficient κ U γ G r ε p.1 p.2) := by
  classical
  have ht : Measurable (fun p : ℝ≥0 × ℂ => (p.1 : WithTop ℝ≥0)) := measurable_fst.withTop_coe
  have hr : Measurable (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 r) :=
    (spatialHitTime_measurable_point h.1 r).comp measurable_snd
  have he : Measurable (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 ε) :=
    (spatialHitTime_measurable_point h.1 ε).comp measurable_snd
  have hm : MeasurableSet {p : ℝ≥0 × ℂ | spatialHitTime γ p.2 r ≤ p.1 ∧
      (p.1 : WithTop ℝ≥0) ≤ spatialHitTime γ p.2 ε ∧ p.2 ∈ survivingDomain γ p.1} :=
    (measurableSet_le hr ht).inter ((measurableSet_le ht he).inter (h.joint_live_measurable hU))
  exact @Measurable.ite _ _ _ _ _ _ (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 r ≤ p.1 ∧
      (p.1 : WithTop ℝ≥0) ≤ spatialHitTime γ p.2 ε ∧ p.2 ∈ survivingDomain γ p.1)
    (fun _ => inferInstance) hm
    (h.green_coefficient_measurable hU hκ) measurable_const

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace SLEExactGauge

 

lemma area_square_tonelli {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    {μ : Measure T} {ν : Measure Z} [SFinite μ] [SFinite ν]
    {f : T × Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, (∫⁻ z, f (t, z) ∂ν) ^ 2 ∂μ) =
      ∫⁻ z, ∫⁻ w, ∫⁻ t, f (t, z) * f (t, w) ∂μ ∂ν ∂ν := by
  have hft (t : T) : Measurable (fun z => f (t, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have h3 : Measurable (fun p : (T × Z) × Z => f (p.1.1, p.1.2) * f (p.1.1, p.2)) :=
    (hf.comp measurable_fst).mul
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hinner : Measurable (fun p : T × Z => ∫⁻ w, f (p.1, p.2) * f (p.1, w) ∂ν) :=
    h3.lintegral_prod_right'
  calc
    _ = ∫⁻ t, ∫⁻ z, ∫⁻ w, f (t, z) * f (t, w) ∂ν ∂ν ∂μ := by
      apply lintegral_congr
      intro t
      simp_rw [lintegral_const_mul _ (hft t)]
      rw [lintegral_mul_const _ (hft t), pow_two]
    _ = ∫⁻ z, ∫⁻ t, ∫⁻ w, f (t, z) * f (t, w) ∂ν ∂μ ∂ν :=
      lintegral_lintegral_swap hinner.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_fst.prodMk measurable_const)).mul hf).aemeasurable

lemma spatial_integral_square_le {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (f : Z → ℝ) :
    ENNReal.ofReal ((∫ z, f z ∂ν) ^ 2) ≤ (∫⁻ z, ENNReal.ofReal |f z| ∂ν) ^ 2 := by
  have he (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal |x| := by
    rw [← ofReal_norm, Real.norm_eq_abs]
  have hb := pow_le_pow_left₀ bot_le (enorm_integral_le_lintegral_enorm (μ := ν) f) 2
  rw [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)] at hb
  simpa only [he] using hb

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

 

theorem IsCapacityTwoWitness.spatial_slab_absolute_bracket_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ t in Ici (0 : ℝ), (∫⁻ z in A,
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|) ^ 2) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  have hb : Measurable (fun p : ℝ × ℂ => spatialSlabCoefficient κ U γ G r ε p.1.toNNReal p.2) := by
    have hm : Measurable (fun p : ℝ × ℂ => (p.1.toNNReal, p.2)) :=
      (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
    exact (h.spatial_slab_coefficient_measurable hU hκ r ε).comp
      (f := fun p : ℝ × ℂ => (p.1.toNNReal, p.2)) hm
  rw [area_square_tonelli hb.abs.ennreal_ofReal]
  have he (t : ℝ) (z w : ℂ) :
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z| *
        ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal w| =
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [he]
  exact h.spatial_slab_pair_area_bound hU hκ hκ4 hε hr A hA hheight

 

theorem IsCapacityTwoWitness.spatial_slab_bracket_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal
      ((∫ z in A, spatialSlabCoefficient κ U γ G r ε t.toNNReal z) ^ 2)) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  exact (lintegral_mono fun t => spatial_integral_square_le (volume.restrict A) _).trans
    (h.spatial_slab_absolute_bracket_bound hU hκ hκ4 hε hr A hA hheight)

end SLEExactGauge

 

 

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianPredictable

 

lemma gaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hf (t : ℝ) : HasDerivAt f ((v : ℝ) * t * f t) t := by
    apply (((hasDerivAt_id t).pow 2 |>.const_mul (v : ℝ)).div_const 2).exp.congr_deriv
    dsimp [f]
    ring
  have hd : deriv f = fun t => (v : ℝ) * t * f t := funext fun t => (hf t).deriv
  have hd1 : deriv (fun t => (v : ℝ) * t * f t) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hf t)).congr_deriv
    simp only [id_eq]
    ring
  have hd2 : deriv (fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ)).mul (hf t)).congr_deriv
    simp only [id_eq, Pi.pow_apply]
    ring
  have hd3 : deriv (fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
        (v : ℝ) ^ 4 * t ^ 4) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply ((((hasDerivAt_id t).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul ((v : ℝ) ^ 3))).mul (hf t)).congr_deriv
    simp only [id_eq, Pi.pow_apply, Pi.add_apply]
    ring
  change (∫ x, ((fun x : ℝ => x) ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (by simp), mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 4 f 0 = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd, hd1, hd2, hd3]
  simp [f]

lemma gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simpa [integral_id_gaussianReal] using hv.symm

lemma gaussian_square_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have h4 := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow
    (p := 4) (by norm_num)
  convert h4 using 1
  funext x
  simp only [id_eq, Real.norm_eq_abs]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]

lemma gaussian_square_variance (v : ℝ≥0) :
    variance (fun x : ℝ => x ^ 2) (gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_sub (gaussian_square_memLp v), gaussian_second_moment]
  have heq : (fun x : ℝ => ((fun x : ℝ => x ^ 2) ^ 2) x) = fun x : ℝ => x ^ 4 := by
    funext x
    simp only [Pi.pow_apply]
    ring
  rw [show (fun x : ℝ => x ^ 2) ^ 2 = (fun x : ℝ => x ^ 4) from heq,
    gaussian_fourth_moment]
  ring

lemma increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t-s)) P := by
  simpa only [add_tsub_cancel_of_le hst] using
    (hB.toIsPreBrownianReal.shift s).hasLaw_eval (t-s)

lemma increment_square_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (fun ω => (B t ω - B s ω) ^ 2) 2 P := by
  have hl := increment_hasLaw hB hst
  exact (hl.map_eq ▸ gaussian_square_memLp (t-s)).comp_of_map hl.aemeasurable

lemma increment_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t-s : ℝ≥0) := by
  have hl := increment_hasLaw hB hst
  simpa only [Function.comp_apply, gaussian_second_moment] using
    hl.integral_comp (show AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      (gaussianReal 0 (t-s)) from by fun_prop)

lemma increment_square_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    variance (fun ω => (B t ω - B s ω) ^ 2) P = 2 * (t-s : ℝ≥0) ^ 2 := by
  have hl := increment_hasLaw hB hst
  rw [← covariance_self (hl.aemeasurable.pow_const 2 : AEMeasurable (fun ω => (B t ω - B s ω) ^ 2) P)]
  change cov[(fun x : ℝ => x ^ 2) ∘ (fun ω => B t ω - B s ω),
    (fun x : ℝ => x ^ 2) ∘ (fun ω => B t ω - B s ω); P] = _
  rw [hl.covariance_comp (by fun_prop) (by fun_prop), covariance_self (by fun_prop),
    gaussian_square_variance]

 

abbrev pastSigma {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (t : Set.Iic s) => B t ω) inferInstance

lemma brownian_indep_of_past_measurable {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s v : ℝ≥0)
    {X : Ω → α} (hX : Measurable[pastSigma B s] X) :
    IndepFun X (fun ω => B (s+v) ω - B s ω) P := by
  have hh := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply v)
  change Indep (MeasurableSpace.comap X inferInstance)
    (MeasurableSpace.comap (fun ω => B (s+v) ω - B s ω) inferInstance) P
  exact indep_of_indep_of_le_left hh hX.comap_le

lemma pastSigma_mono {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : pastSigma B s ≤ pastSigma B t := by
  let : MeasurableSpace Ω := pastSigma B t
  have hm : Measurable (fun ω (u : Set.Iic s) => B u ω) := by
    apply Measurable.of_eval
    intro u
    exact (measurable_pi_apply (⟨u, u.2.trans hst⟩ : Set.Iic t)).comp
      (comap_measurable (fun ω (v : Set.Iic t) => B v ω))
  exact hm.comap_le

lemma past_measurable_eval {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : Measurable[pastSigma B t] (B s) :=
  (measurable_pi_apply (⟨s, hst⟩ : Set.Iic t)).comp
    (comap_measurable (fun ω (v : Set.Iic t) => B v ω))

lemma past_mul_feature_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) {X : Ω → ℝ}
    (hX : Measurable[pastSigma B s] X) (hXa : AEMeasurable X P)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ ω, X ω * φ (B t ω - B s ω) ∂P) =
      (∫ ω, X ω ∂P) * (∫ x, φ x ∂gaussianReal 0 (t-s)) := by
  have hi := (brownian_indep_of_past_measurable hB s (t-s) hX).comp
    measurable_id hφ
  rw [add_tsub_cancel_of_le hst] at hi
  have hl := increment_hasLaw hB hst
  change IndepFun X (fun ω => φ (B t ω - B s ω)) P at hi
  rw [hi.integral_fun_mul_eq_mul_integral hXa.aestronglyMeasurable
      (hφ.comp_aemeasurable hl.aemeasurable).aestronglyMeasurable]
  rw [show (∫ ω, φ (B t ω - B s ω) ∂P) = ∫ x, φ x ∂gaussianReal 0 (t-s) from
    hl.integral_comp hφ.aestronglyMeasurable]

lemma independent_product_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXY : IndepFun X Y P) : MemLp (fun ω => X ω * Y ω) 2 P := by
  apply (memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2
  have hi := (hXY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hX.integrable_sq hY.integrable_sq
  convert hi using 1
  ext ω
  simp only [Function.comp_apply, Pi.mul_apply, mul_pow, id_eq]

 
def predictableFeatureSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (C : ℕ → Ω → ℝ) (φ : ℕ → ℝ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, C i ω * φ i (B (t (i+1)) ω - B (t i) ω)

lemma predictableTerm_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i))) (i : ℕ) :
    MemLp (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) 2 P := by
  have ht' := ht (Nat.le_succ i)
  have hl := increment_hasLaw hB ht'
  have hY := (hl.map_eq ▸ hφ2 i).comp_of_map hl.aemeasurable
  have hi := (brownian_indep_of_past_measurable hB (t i) (t (i+1)-t i) (hC i)).comp
    measurable_id (hφ i)
  rw [add_tsub_cancel_of_le ht'] at hi
  exact independent_product_memLp_two (hC2 i) hY hi

lemma predictableTerm_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hCa : ∀ i, AEMeasurable (C i) P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0) (i : ℕ) :
    (∫ ω, C i ω * φ i (B (t (i+1)) ω - B (t i) ω) ∂P) = 0 := by
  rw [past_mul_feature_integral hB (ht (Nat.le_succ i)) (hC i) (hCa i) (φ i) (hφ i),
    hφ0, mul_zero]

lemma predictableTerm_past_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i))
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i)) {i j : ℕ} (hij : i+1 ≤ j) :
    Measurable[pastSigma B (t j)]
      (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) := by
  have hi : t i ≤ t j := ht (le_trans (Nat.le_succ i) hij)
  exact ((hC i).mono (pastSigma_mono B hi) le_rfl).mul
    ((hφ i).comp ((past_measurable_eval B (ht hij)).sub
      (past_measurable_eval B hi)))

lemma predictableTerm_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i)))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0)
    {i j : ℕ} (hij : i ≠ j) :
    covariance (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω))
      (fun ω => C j ω * φ j (B (t (j+1)) ω - B (t j) ω)) P = 0 := by
  wlog hlt : i < j generalizing i j
  · rw [covariance_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  have hAi := predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 i
  have hAj := predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 j
  rw [covariance_eq_sub hAi hAj,
    predictableTerm_integral hB t ht C hC (fun i => (hC2 i).aemeasurable) φ hφ hφ0 i,
    zero_mul, sub_zero]
  have hp := (predictableTerm_past_measurable B t ht C hC φ hφ hlt).mul (hC j)
  have hh := past_mul_feature_integral hB (ht (Nat.le_succ j)) hp
    (hAi.aemeasurable.mul (hC2 j).aemeasurable) (φ j) (hφ j)
  rw [hφ0, mul_zero] at hh
  convert hh using 1
  congr 1
  ext ω
  simp only [Pi.mul_apply]
  ring

end SLEExactGauge.BrownianPredictable
end
end
end

end OAI
