import Mathlib

namespace OAI

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology RealInnerProductSpace

namespace Problem358.MovingCellTrace

/-- The indicator of a nonnegative affine cut. -/
def cutIndicator (r : ℝ) : ℝ := (Set.Ici (0 : ℝ)).indicator (fun _ => 1) r

lemma continuousAt_cutIndicator {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt cutIndicator r := by
  apply ContinuousOn.continuousAt_indicator continuousOn_const
  simpa only [frontier_Ici, Set.mem_singleton_iff] using hr

/-- A finite family of cuts is stable whenever every limiting score is nonzero. -/
lemma tendsto_cut_product {α ι : Type*} {l : Filter α}
    (J : Finset ι) {s : α → ι → ℝ} {b : ι → ℝ}
    (hs : ∀ i ∈ J, Tendsto (fun a => s a i) l (𝓝 (b i)))
    (hb : ∀ i ∈ J, b i ≠ 0) :
    Tendsto (fun a => ∏ i ∈ J, cutIndicator (s a i)) l
      (𝓝 (∏ i ∈ J, cutIndicator (b i))) := by
  exact tendsto_finsetProd J fun i hi =>
    (continuousAt_cutIndicator (hb i hi)).tendsto.comp (hs i hi)

/-- Generic scaled-trace convergence for the unchanged source constraint and all
nonselected moving cuts. The selected face is deliberately absent from `J`. -/
lemma tendsto_remainder_trace {α ι X : Type*} [TopologicalSpace X]
    {l : Filter α} (J : Finset ι) {K : Set X} {w : X → ℝ}
    {x : α → X} {z : X} {s : α → ι → ℝ} {b : ι → ℝ}
    (hx : Tendsto x l (𝓝 z)) (hz : z ∉ frontier K)
    (hw : ContinuousOn w (interior K))
    (hs : ∀ i ∈ J, Tendsto (fun a => s a i) l (𝓝 (b i)))
    (hb : ∀ i ∈ J, b i ≠ 0) :
    Tendsto (fun a => K.indicator w (x a) * ∏ i ∈ J, cutIndicator (s a i)) l
      (𝓝 (K.indicator w z * ∏ i ∈ J, cutIndicator (b i))) := by
  exact ((hw.continuousAt_indicator hz).tendsto.comp hx).mul
    (tendsto_cut_product J hs hb)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Affine-score specialization. This permits all sites and intercepts, and the
rescaled observation point, to move simultaneously. -/
lemma tendsto_affine_remainder_trace {α ι : Type*} {l : Filter α}
    (J : Finset ι) (i : ι) {K : Set F} {w : F → ℝ}
    {x : α → F} {z : F} {y : α → ι → F} {y₀ : ι → F}
    {c : α → ι → ℝ} {c₀ : ι → ℝ}
    (hx : Tendsto x l (𝓝 z)) (hz : z ∉ frontier K)
    (hw : ContinuousOn w (interior K))
    (hy : ∀ k, Tendsto (fun a => y a k) l (𝓝 (y₀ k)))
    (hc : ∀ k, Tendsto (fun a => c a k) l (𝓝 (c₀ k)))
    (hneq : ∀ k ∈ J, ⟪z, y₀ i - y₀ k⟫ + c₀ i - c₀ k ≠ 0) :
    Tendsto (fun a => K.indicator w (x a) * ∏ k ∈ J,
      cutIndicator (⟪x a, y a i - y a k⟫ + c a i - c a k)) l
      (𝓝 (K.indicator w z * ∏ k ∈ J,
        cutIndicator (⟪z, y₀ i - y₀ k⟫ + c₀ i - c₀ k))) := by
  apply tendsto_remainder_trace J hx hz hw _ hneq
  intro k _
  exact ((hx.inner ((hy i).sub (hy k))).add (hc i)).sub (hc k)

/-- The two-sided scaled path required by moving-halfspace differentiation. -/
lemma tendsto_scaled_affine_remainder_trace {ι : Type*}
    (J : Finset ι) (i : ι) (y v : ι → F) (c r : ι → ℝ)
    {K : Set F} {w : F → ℝ} {z : F} (n : F) (u : ℝ)
    (hz : z ∉ frontier K) (hw : ContinuousOn w (interior K))
    (hneq : ∀ k ∈ J, ⟪z, y i - y k⟫ + c i - c k ≠ 0) :
    Tendsto (fun h : ℝ => K.indicator w (z + h • (u • n)) * ∏ k ∈ J,
      cutIndicator (⟪z + h • (u • n), (y i + h • v i) - (y k + h • v k)⟫ +
        (c i + h * r i) - (c k + h * r k))) (𝓝 0)
      (𝓝 (K.indicator w z * ∏ k ∈ J,
        cutIndicator (⟪z, y i - y k⟫ + c i - c k))) := by
  apply tendsto_affine_remainder_trace J i (y₀ := y) (c₀ := c) _ hz hw _ _ hneq
  · have hcont : Continuous (fun h : ℝ => z + h • (u • n)) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  · intro k
    have hcont : Continuous (fun h : ℝ => y k + h • v k) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto 0
  · intro k
    have hcont : Continuous (fun h : ℝ => c k + h * r k) := by fun_prop
    simpa only [zero_mul, add_zero] using hcont.tendsto 0

end Problem358.MovingCellTrace

end

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Problem358.MovingCellTrace

lemma measurable_cutIndicator : Measurable cutIndicator :=
  measurable_const.indicator measurableSet_Ici

lemma norm_cutIndicator_le_one (r : ℝ) : ‖cutIndicator r‖ ≤ 1 := by
  by_cases hr : 0 ≤ r <;> simp [cutIndicator, Set.indicator, hr]

lemma norm_cut_product_le_one {ι : Type*} (J : Finset ι) (s : ι → ℝ) :
    ‖∏ i ∈ J, cutIndicator (s i)‖ ≤ 1 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_cutIndicator_le_one _)).trans ih

lemma measurable_cut_product {ι X : Type*} [MeasurableSpace X]
    (J : Finset ι) {s : X → ι → ℝ} (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Measurable (fun x => ∏ i ∈ J, cutIndicator (s x i)) :=
  J.measurable_prod (fun i hi => measurable_cutIndicator.comp (hs i hi))

lemma measurable_remainder {ι X : Type*} [MeasurableSpace X]
    (J : Finset ι) {K : Set X} (hK : MeasurableSet K)
    {w : X → ℝ} (hw : Measurable w) {s : X → ι → ℝ}
    (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Measurable (fun x => K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)) :=
  (hw.indicator hK).mul (measurable_cut_product J hs)

/-- Removing finitely many halfspace constraints never enlarges the absolute weight. -/
lemma norm_remainder_le {ι X : Type*} (J : Finset ι) (K : Set X)
    (w : X → ℝ) (s : X → ι → ℝ) (x : X) :
    ‖K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)‖ ≤ ‖K.indicator w x‖ := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_cut_product_le_one J (s x))
    (norm_nonneg _)).trans_eq (mul_one _)

lemma integrable_remainder {ι X : Type*} [MeasurableSpace X]
    {μ : Measure X} (J : Finset ι) {K : Set X} (hK : MeasurableSet K)
    {w : X → ℝ} (hw : IntegrableOn w K μ) {s : X → ι → ℝ}
    (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Integrable (fun x => K.indicator w x * ∏ i ∈ J, cutIndicator (s x i)) μ := by
  have hwi := hw.integrable_indicator hK
  apply hwi.norm.mono' (hwi.aestronglyMeasurable.mul
    (measurable_cut_product J hs).aestronglyMeasurable)
  exact Eventually.of_forall (norm_remainder_le J K w s)

/-- Ambient integrability transfers to any measure-preserving product chart. -/
lemma integrable_remainder_comp_measurePreserving
    {ι X V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    {μ : Measure X} {ν : Measure V} {chart : X → V}
    (hchart : MeasurePreserving chart μ ν)
    (J : Finset ι) {K : Set V} (hK : MeasurableSet K)
    {w : V → ℝ} (hw : IntegrableOn w K ν) {s : V → ι → ℝ}
    (hs : ∀ i ∈ J, Measurable (fun x => s x i)) :
    Integrable (fun p => K.indicator w (chart p) * ∏ i ∈ J,
      cutIndicator (s (chart p) i)) μ := by
  have hi := integrable_remainder J hK hw hs
  exact (hchart.integrable_comp hi.aestronglyMeasurable).2 hi

/-- The transverse support of every cut remainder is inside the projection of the
fixed compact source. No bound on the normal coordinate is needed. -/
lemma norm_remainder_chart_le {ι X V : Type*}
    (J : Finset ι) (K : Set V) (P : V → X) (chart : X × ℝ → V)
    (hP : ∀ z t, P (chart (z, t)) = z)
    (w : V → ℝ) (s : V → ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ x ∈ K, ‖w x‖ ≤ C) (z : X) (t : ℝ) :
    ‖K.indicator w (chart (z, t)) * ∏ i ∈ J,
      cutIndicator (s (chart (z, t)) i)‖ ≤ (P '' K).indicator (fun _ => C) z := by
  classical
  by_cases hx : chart (z, t) ∈ K
  · have hz : z ∈ P '' K := ⟨chart (z, t), hx, hP z t⟩
    rw [Set.indicator_of_mem hz]
    exact (norm_remainder_le J K w s (chart (z, t))).trans (by
      simpa only [Set.indicator_of_mem hx] using hw (chart (z, t)) hx)
  · simp only [Set.indicator_of_notMem hx, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hC) z

/-- Any continuous speed envelope is integrable against a compact transverse
support bound. This is the domination premise in the moving-face kernel. -/
lemma integrable_compact_projection_bound
    {X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] [TopologicalSpace V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set V} (hK : IsCompact K) {P : V → X} (hP : Continuous P)
    {A : X → ℝ} (hA : Continuous A) (C : ℝ) :
    Integrable (fun z => A z * (P '' K).indicator (fun _ => C) z) μ := by
  have hcompact : IsCompact (P '' K) := hK.image hP
  have hint : Integrable ((P '' K).indicator (fun z => A z * C)) μ :=
    ((hA.mul continuous_const).continuousOn.integrableOn_compact hcompact).integrable_indicator
      hcompact.measurableSet
  convert hint using 1
  funext z
  by_cases hz : z ∈ P '' K <;> simp [Set.indicator, hz]

/-- Compactness discharges a uniform transverse dominating function for every
configuration of additional halfspace cuts, at once. -/
theorem exists_compact_projection_domination
    {ι Θ X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] [TopologicalSpace V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (J : Finset ι) {K : Set V} (hK : IsCompact K)
    {P : V → X} (hP : Continuous P) (chart : X × ℝ → V)
    (hchart : ∀ z t, P (chart (z, t)) = z)
    {w : V → ℝ} (hw : ContinuousOn w K)
    (s : Θ → V → ι → ℝ) {A : X → ℝ} (hA : Continuous A) :
    ∃ B : X → ℝ, (∀ z, 0 ≤ B z) ∧ Integrable (fun z => A z * B z) μ ∧
      ∀ a z t, ‖K.indicator w (chart (z, t)) * ∏ i ∈ J,
        cutIndicator (s a (chart (z, t)) i)‖ ≤ B z := by
  obtain ⟨C, hC, hbound⟩ := (hK.image_of_continuousOn hw).isBounded.exists_pos_norm_le
  refine ⟨(P '' K).indicator (fun _ => C), ?_,
    integrable_compact_projection_bound hK hP hA C, ?_⟩
  · exact fun z => Set.indicator_nonneg (fun _ _ => hC.le) z
  · intro a z t
    exact norm_remainder_chart_le J K P chart hchart w (s a) hC.le
      (fun x hx => hbound (w x) ⟨x, hx, rfl⟩) z t

end Problem358.MovingCellTrace

namespace Problem358.MovingCellTrace

/-- Continuity of finite-cut face integrals in a fixed transverse projection.
All integrability and domination are consequences of the compact source and
continuous test weight. The varying charts need not be measure preserving: the
measure here stays on the fixed reference plane. -/
theorem tendsto_integral_remainder_of_compact_projection
    {ι α X V : Type*} {l : Filter α} [l.IsCountablyGenerated]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] [T2Space V]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (J : Finset ι) {K : Set V} (hK : IsCompact K)
    {P : V → X} (hP : Continuous P)
    {chart : α → X → V} {base : X → V}
    (hproject : ∀ q x, P (chart q x) = x)
    (hchartmeas : ∀ q, Measurable (chart q))
    (hchartlim : ∀ᵐ x ∂μ, Tendsto (fun q => chart q x) l (𝓝 (base x)))
    {w : V → ℝ} (hwmeas : Measurable w) (hwcont : ContinuousOn w K)
    {s : α → V → ι → ℝ} {b : X → ι → ℝ}
    (hsmeas : ∀ q k, k ∈ J → Measurable (fun v => s q v k))
    (hslim : ∀ᵐ x ∂μ, ∀ k ∈ J,
      Tendsto (fun q => s q (chart q x) k) l (𝓝 (b x k)))
    (hregular : ∀ᵐ x ∂μ, base x ∉ frontier K ∧ ∀ k ∈ J, b x k ≠ 0) :
    Tendsto (fun q => ∫ x, K.indicator w (chart q x) * ∏ k ∈ J,
      cutIndicator (s q (chart q x) k) ∂μ) l
      (𝓝 (∫ x, K.indicator w (base x) * ∏ k ∈ J, cutIndicator (b x k) ∂μ)) := by
  obtain ⟨C, hC, hCbound⟩ := (hK.image_of_continuousOn hwcont).isBounded.exists_pos_norm_le
  let B : X → ℝ := (P '' K).indicator (fun _ => C)
  have hBint : Integrable B μ := by
    simpa only [one_mul] using
      (integrable_compact_projection_bound hK hP continuous_const C :
        Integrable (fun x => (1 : ℝ) * (P '' K).indicator (fun _ => C) x) μ)
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBint ?_
  · exact Eventually.of_forall fun q =>
      ((measurable_remainder J hK.measurableSet hwmeas (hsmeas q)).comp
        (hchartmeas q)).aestronglyMeasurable
  · exact Eventually.of_forall fun q => Eventually.of_forall fun x =>
      norm_remainder_chart_le J K P (fun p : X × ℝ => chart q p.1)
        (fun z _ => hproject q z) w (s q) hC.le
        (fun v hv => hCbound (w v) ⟨v, hv, rfl⟩) x 0
  · filter_upwards [hchartlim, hslim, hregular] with x hx hs hr
    exact tendsto_remainder_trace J hx hr.1
      (hwcont.mono interior_subset) hs hr.2

end Problem358.MovingCellTrace

end

end OAI
