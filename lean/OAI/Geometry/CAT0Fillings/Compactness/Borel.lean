import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Compactness.Ascoli
import OAI.Geometry.CAT0Fillings.Compactness.Coordinates
import OAI.Geometry.CAT0Fillings.Compactness.Projected

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma mul_bounded {b u : X → ℝ} {B U : ℝ≥0}
    (hb : ∀ x, |b x| ≤ B) (hu : ∀ x, |u x| ≤ U) (x : X) : |b x*u x| ≤ (B*U:ℝ≥0) := by
  rw [abs_mul]
  exact mul_le_mul (hb x) (hu x) (abs_nonneg _) B.coe_nonneg

theorem totallyBounded_borel_projected {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ i, LipschitzWith (L i) (u i))
    (hU : ∀ i x, |u i x| ≤ U i)
    {χ : X → ℝ} (hχ : Measurable χ) (B : ℝ≥0) (hB : ∀ x, |χ x| ≤ B)
    (M : ℝ≥0) (hMv : ∀ i, ‖value (hT := hT) (hu i)‖ ≤ M)
    (hMg : ∀ i, ‖q.gradient (hu i)‖ ≤ M) :
    TotallyBounded (range fun i => projectedL1 h hX π hπ (hχ.mul (hu i).continuous.measurable)
      (B*U i) (mul_bounded hB (hU i))) := by
  have hχ2 : MemLp χ 2 (currentMassMeasure hT) := MemLp.of_bound hχ.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  obtain ⟨b,hb⟩ := exists_lipschitz_L2_approximation (currentMassMeasure hT) hχ2
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  have hlim : Tendsto (fun j => (K:ℝ)^(k+1)*lpNorm (fun x => (b j).val x-χ x) 2 (currentMassMeasure hT)*M)
      atTop (𝓝 0) := by simpa using (hb.const_mul ((K:ℝ)^(k+1))).mul_const (M:ℝ)
  obtain ⟨j,hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨C₀,hC₀⟩ := (b j).property.2
  let C : ℝ≥0 := ⟨max C₀ 0,le_max_right _ _⟩
  have hC x : |(b j).val x| ≤ C := (hC₀ x).trans (le_max_left _ _)
  obtain ⟨J,hJ⟩ := (b j).property.1
  let g i := projectedL1 h hX π hπ ((b j).val.continuous.measurable.mul (hu i).continuous.measurable)
    (C*U i) (mul_bounded hC (hU i))
  refine ⟨g,?_,?_⟩
  · have he : g = fun i =>
        (fullSlice_eval_integrable h hX π (fun a => boundedLip_of_lipschitz (hπ a))
          ((boundedLip_of_lipschitz hJ).mul (boundedLip_of_lipschitz (hu i))) (fun j => Fin.elim0 j)).toL1
            (fun z => fullSlice h π z (fun x => (b j).val x*u i x) (fun j => Fin.elim0 j)) := by
      funext i
      exact projectedL1_lipschitz h hX π hπ ((b j).property.mul (boundedLip_of_lipschitz (hu i))) _
    rw [he]
    exact q.totallyBounded_whole_projected h hz hX π hπ u L hu hJ M hMv hMg
  · intro i
    rw [dist_comm]
    change dist (projectedL1 h hX π hπ _ _ _) (projectedL1 h hX π hπ _ _ _) < ε
    rw [dist_projectedL1]
    apply (fullSlice_cutoff_difference_bound h hX π hπ (b j).val.continuous.measurable hχ
      (hu i).continuous.measurable hC hB (hU i)).trans_lt
    apply lt_of_le_of_lt _ hj
    rw [←norm_value (hT := hT) (hu i)]
    exact mul_le_mul_of_nonneg_left (hMv i) (mul_nonneg (pow_nonneg K.coe_nonneg _) lpNorm_nonneg)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma coordinate_distance_le (h : NormalApprox (k+1) T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin (k+1) → X → ℝ) {K J : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hJ : LipschitzWith J (q.chart i).param)
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u v : X → ℝ} {L P : ℝ≥0} (hu : LipschitzWith L u) (hv : LipschitzWith P v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu.continuous.measurable U hU) (q.coordinateL1 i hv.continuous.measurable V hV) ≤
      (J:ℝ)^(k+1)*dist (q.isolatedL1 h hX i F hF hu.continuous.measurable U hU)
        (q.isolatedL1 h hX i F hF hv.continuous.measurable V hV) := by
  rw [q.dist_coordinateL1,q.dist_isolatedL1 h hX i F hF hFinv hjac hu hv,←integral_const_mul]
  have hb x : abs |u x-v x| ≤ (U+V:ℝ≥0) := by
    rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hU x) (hV x))
  have hm := (hu.continuous.measurable.sub hv.continuous.measurable).norm
  have hleft := integrable_weighted_comp (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.density_integrable i) hm ⟨(U+V:ℝ≥0),hb⟩
  have hright := integrable_weighted_comp (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.chart i).integrable.norm hm ⟨(U+V:ℝ≥0),hb⟩
  apply integral_mono_ae (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hleft)
    (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hright.const_mul ((J:ℝ)^(k+1)))
  filter_upwards [q.ae_chart_jacobian_le i hJ] with z hz
  dsimp only [density]
  calc _ ≤ |((q.chart i).multiplicity z:ℝ)| * ((J:ℝ)^(k+1))*|u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

theorem totallyBounded_coordinate {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M) (i : ℕ) :
    TotallyBounded (range fun j => q.coordinateL1 i (hu j).continuous.measurable (U j) (hU j)) := by
  obtain ⟨F,K,hF,hFinv,hjac⟩ := q.exists_exact_inverse_coordinates i
  obtain ⟨J,J',hJ,hJ'⟩ := (q.chart i).bilipschitz
  have hib : ∀ x, |(q.chart i).image.indicator (fun _ => (1:ℝ)) x| ≤ (1:ℝ≥0) := by
    intro x; by_cases hx : x ∈ (q.chart i).image <;> simp [hx]
  have ht := q.totallyBounded_borel_projected h hz hX F hF u L U hu hU
    (measurable_const.indicator (q.chart i).measurableSet_image) 1 hib M hMv hMg
  have he : (fun j => projectedL1 h hX F hF ((measurable_const.indicator (q.chart i).measurableSet_image).mul (hu j).continuous.measurable) (1*U j) (mul_bounded hib (hU j))) =
      (fun j => q.isolatedL1 h hX i F hF (hu j).continuous.measurable (U j) (hU j)) := by
    funext j
    apply Lp.ext
    filter_upwards [(fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a))
      ((measurable_const.indicator (q.chart i).measurableSet_image).mul (hu j).continuous.measurable)
      (1*U j) (mul_bounded hib (hU j))).1.coeFn_toL1,
      (fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a))
      ((hu j).continuous.measurable.indicator (q.chart i).measurableSet_image)
      (U j) (q.indicator_bound i (hU j))).1.coeFn_toL1] with z hz hz'
    change _ = _ at hz hz'
    dsimp only [projectedL1,isolatedL1]
    rw [hz,hz']
    congr 2
    ext x
    by_cases hx : x ∈ (q.chart i).image <;> simp [hx]
  rw [he] at ht
  apply totallyBounded_range_of_control ht
  intro ε hε
  refine ⟨ε/((J:ℝ)^(k+1)+1),div_pos hε (by positivity),?_⟩
  intro a b hab
  apply (q.coordinate_distance_le h hX i F hF hJ hFinv hjac (hu a) (hu b) (U a) (U b) (hU a) (hU b)).trans_lt
  have hc := (lt_div_iff₀ (show 0 < (J:ℝ)^(k+1)+1 by positivity)).mp hab
  have hd : 0 ≤ dist (q.isolatedL1 h hX i F hF (hu a).continuous.measurable (U a) (hU a))
    (q.isolatedL1 h hX i F hF (hu b).continuous.measurable (U b) (hU b)) := dist_nonneg
  nlinarith [pow_nonneg J.coe_nonneg (k+1)]

end CAT0Fillings.ChartGeometry
end

end OAI
