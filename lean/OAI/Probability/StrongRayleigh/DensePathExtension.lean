import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal

namespace Problem336AdditiveD139.DensePathExtension

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def restrictPath {D : Type u_1} (e : D → ℝ≥0) (f : C(ℝ≥0, ℝ)) : D → ℝ :=
  fun d => f (e d)

lemma measurable_restrictPath {D : Type u_2} (e : D → ℝ≥0) :
    Measurable (restrictPath e) := by
  exact Measurable.of_eval (fun d => (continuous_eval_const (e d)).measurable)

lemma injective_restrictPath {D : Type u_3} (e : D → ℝ≥0) (he : DenseRange e) :
    Injective (restrictPath e) := by
  intro f g h
  apply ContinuousMap.ext
  exact congr_fun (he.equalizer f.continuous g.continuous h)

lemma measurableEmbedding_restrictPath {D : Type u_4} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableEmbedding (restrictPath e) :=
  (measurable_restrictPath e).measurableEmbedding (injective_restrictPath e he)

def Continuable {D : Type u_5} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∃ f : C(ℝ≥0, ℝ), restrictPath e f = x

lemma measurableSet_continuable {D : Type u_6} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableSet {x | Continuable e x} :=
  (measurableEmbedding_restrictPath e he).measurableSet_range

def extendPath {D : Type u_7} (e : D → ℝ≥0) : (D → ℝ) → C(ℝ≥0, ℝ) :=
  Function.extend (restrictPath e) id (fun _ => 0)

lemma measurable_extendPath {D : Type u_8} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : Measurable (extendPath e) :=
  (measurableEmbedding_restrictPath e he).measurable_extend measurable_id measurable_const

@[simp] lemma extendPath_restrictPath {D : Type u_9}
    (e : D → ℝ≥0) (he : DenseRange e) (f : C(ℝ≥0, ℝ)) :
    extendPath e (restrictPath e f) = f :=
  (injective_restrictPath e he).extend_apply id (fun _ => 0) f

lemma restrictPath_extendPath {D : Type u_10}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : Continuable e x) :
    restrictPath e (extendPath e x) = x := by
  rcases hx with ⟨f, rfl⟩
  rw [extendPath_restrictPath e he]

lemma extendPath_eq_zero_of_not_continuable {D : Type u_11}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : ¬ Continuable e x) : extendPath e x = 0 := by
  exact Function.extend_apply' _ _ _ hx

def LocalCauchyData {D : Type u_12} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∀ t : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ i j : D, dist (e i) t < δ → dist (e j) t < δ → dist (x i) (x j) < ε

lemma continuable_of_localCauchyData {D : Type u_13}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : LocalCauchyData e x) :
    Continuable e x := by
  let : TopologicalSpace D := TopologicalSpace.induced e inferInstance
  have hd : IsDenseInducing e := ⟨⟨rfl⟩, he⟩
  have hc (t : ℝ≥0) : Cauchy (Filter.map x (Filter.comap e (𝓝 t))) := by
    refine Metric.cauchy_iff.mpr ⟨(hd.comap_nhds_neBot t).map x, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hx t ε hε
    refine ⟨x '' (e ⁻¹' Metric.ball t δ),
      Filter.image_mem_map (Filter.preimage_mem_comap (Metric.ball_mem_nhds t hδ)), ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact hmod i j hi hj
  have hlim (t : ℝ≥0) : ∃ a : ℝ, Tendsto x (Filter.comap e (𝓝 t)) (𝓝 a) :=
    CompleteSpace.complete (hc t)
  refine ⟨⟨hd.extend x, hd.continuous_extend hlim⟩, ?_⟩
  exact funext (hd.extend_eq' hlim)

lemma localCauchyData_of_continuable {D : Type u_14}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : Continuable e x) : LocalCauchyData e x := by
  rcases hx with ⟨f, rfl⟩
  intro t ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt (ε / 2)
    (half_pos hε)
  refine ⟨δ, hδ, fun i j hi hj => ?_⟩
  calc
    dist (f (e i)) (f (e j)) ≤ dist (f (e i)) (f t) + dist (f t) (f (e j)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hmod hi) (by simpa [dist_comm] using hmod hj)
    _ = ε := by ring

lemma continuable_iff_localCauchyData {D : Type u_15}
    (e : D → ℝ≥0) (he : DenseRange e) (x : D → ℝ) :
    Continuable e x ↔ LocalCauchyData e x :=
  ⟨localCauchyData_of_continuable e, continuable_of_localCauchyData e he⟩

lemma measurableSet_localCauchyData {D : Type u_16} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) : MeasurableSet {x | LocalCauchyData e x} := by
  simpa only [← continuable_iff_localCauchyData e he] using measurableSet_continuable e he

def UniformOnBoundedData {D : Type u_17} (e : D → ℝ≥0) (x : D → ℝ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ i j : D, e i ≤ N → e j ≤ N → dist (e i) (e j) < δ → dist (x i) (x j) < ε

lemma localCauchyData_of_uniformOnBoundedData {D : Type u_18}
    (e : D → ℝ≥0) {x : D → ℝ} (hx : UniformOnBoundedData e x) :
    LocalCauchyData e x := by
  intro t ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((t : ℝ) + 1)
  obtain ⟨δ, hδ, hmod⟩ := hx N ε hε
  refine ⟨min 1 (δ / 2), lt_min zero_lt_one (half_pos hδ), fun i j hi hj => ?_⟩
  have hi1 : dist (e i) t < 1 := lt_of_lt_of_le hi (min_le_left _ _)
  have hj1 : dist (e j) t < 1 := lt_of_lt_of_le hj (min_le_left _ _)
  have hiN : e i ≤ N := by
    rw [NNReal.dist_eq, abs_sub_lt_iff] at hi1
    exact_mod_cast (show (e i : ℝ) ≤ N by linarith [hi1.1])
  have hjN : e j ≤ N := by
    rw [NNReal.dist_eq, abs_sub_lt_iff] at hj1
    exact_mod_cast (show (e j : ℝ) ≤ N by linarith [hj1.1])
  apply hmod i j hiN hjN
  calc
    dist (e i) (e j) ≤ dist (e i) t + dist t (e j) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add
      (lt_of_lt_of_le hi (min_le_right _ _))
      (by simpa [dist_comm] using lt_of_lt_of_le hj (min_le_right 1 (δ / 2)))
    _ = δ := by ring

lemma continuable_of_uniformOnBoundedData {D : Type u_19}
    (e : D → ℝ≥0) (he : DenseRange e) {x : D → ℝ} (hx : UniformOnBoundedData e x) :
    Continuable e x :=
  continuable_of_localCauchyData e he (localCauchyData_of_uniformOnBoundedData e hx)

def liftLaw {D : Type u_20} [Countable D] (e : D → ℝ≥0) (he : DenseRange e)
    (μ : ProbabilityMeasure (D → ℝ)) : ProbabilityMeasure C(ℝ≥0, ℝ) :=
  ⟨(μ : Measure (D → ℝ)).map (extendPath e), ⟨by
    rw [Measure.map_apply (measurable_extendPath e he) MeasurableSet.univ]
    simp⟩⟩

lemma map_restrictPath_liftLaw {D : Type u_21} [Countable D]
    (e : D → ℝ≥0) (he : DenseRange e) (μ : ProbabilityMeasure (D → ℝ))
    (hμ : ∀ᵐ x ∂(μ : Measure (D → ℝ)), Continuable e x) :
    Measure.map (restrictPath e) (liftLaw e he μ : Measure C(ℝ≥0, ℝ)) =
      (μ : Measure (D → ℝ)) := by
  change Measure.map (restrictPath e)
    (Measure.map (extendPath e) (μ : Measure (D → ℝ))) = _
  rw [Measure.map_map (measurable_restrictPath e) (measurable_extendPath e he)]
  calc
    Measure.map (restrictPath e ∘ extendPath e) (μ : Measure (D → ℝ)) =
        Measure.map id (μ : Measure (D → ℝ)) :=
      Measure.map_congr (hμ.mono fun x hx => restrictPath_extendPath e he hx)
    _ = _ := Measure.map_id

theorem exists_measurable_path_realization {D : Type u_22} {Ω : Type u_23} [Countable D] [MeasurableSpace Ω]
    (e : D → ℝ≥0) (he : DenseRange e) (P : Measure Ω) (X : Ω → D → ℝ)
    (hX : Measurable X) (hc : ∀ᵐ ω ∂P, LocalCauchyData e (X ω)) :
    ∃ Y : Ω → C(ℝ≥0, ℝ), Measurable Y ∧
      ∀ᵐ ω ∂P, ∀ d : D, Y ω (e d) = X ω d := by
  refine ⟨extendPath e ∘ X, (measurable_extendPath e he).comp hX, ?_⟩
  filter_upwards [hc] with ω hω
  exact congr_fun (restrictPath_extendPath e he (continuable_of_localCauchyData e he hω))

end Problem336AdditiveD139.DensePathExtension

end

end OAI
