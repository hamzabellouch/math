import Mathlib
import OAI.Geometry.CAT0Fillings.Compactness.ChartDensity

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}

lemma fullSlice_borel_sub (h : NormalApprox k T) (π : Fin k → X → ℝ) (z : Euc k)
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    currentBorelAction (fullSlice h π z) (fun x => b x-c x) (fun j => Fin.elim0 j) =
      currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j) := by
  simp only [currentBorelAction_eq (fullSlice_approx h π z).metric]
  exact borelAction_sub _ (fullSlice_approx h π z).metric
    (integrable_bounded_measurable _ hb hB) (integrable_bounded_measurable _ hc hC) _
    (fun j => Fin.elim0 j)

lemma fullSlice_borel_difference_bound (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    (∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j)|) ≤
        (K:ℝ)^k*∫ x, |b x-c x| ∂currentMassMeasure h.metric := by
  have hd x : |b x-c x| ≤ (B+C:ℝ≥0) :=
    (abs_sub _ _).trans (add_le_add (hB x) (hC x))
  have hh := fullSlice_borel_L1_bound h hX π hπ (hb.sub hc) (B+C) hd
  change (∫ z, |currentBorelAction (fullSlice h π z) (fun x => b x-c x) (fun j => Fin.elim0 j)|) ≤
    (K:ℝ)^k*∫ x, |b x-c x| ∂currentMassMeasure h.metric at hh
  simp only [fullSlice_borel_sub h π _ hb hc hB hC] at hh
  exact hh

lemma fullSlice_cutoff_difference_bound (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c u : X → ℝ} (hb : Measurable b) (hc : Measurable c) (hu : Measurable u)
    {B C U : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) (hU : ∀ x, |u x| ≤ U) :
    (∫ z, |currentBorelAction (fullSlice h π z) (fun x => b x*u x) (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) (fun x => c x*u x) (fun j => Fin.elim0 j)|) ≤
        (K:ℝ)^k*lpNorm (fun x => b x-c x) 2 (currentMassMeasure h.metric)*
          lpNorm u 2 (currentMassMeasure h.metric) := by
  have hbu x : |b x*u x| ≤ (B*U:ℝ≥0) := by
    rw [abs_mul]; exact mul_le_mul (hB x) (hU x) (abs_nonneg _) B.coe_nonneg
  have hcu x : |c x*u x| ≤ (C*U:ℝ≥0) := by
    rw [abs_mul]; exact mul_le_mul (hC x) (hU x) (abs_nonneg _) C.coe_nonneg
  apply (fullSlice_borel_difference_bound h hX π hπ (hb.mul hu) (hc.mul hu) hbu hcu).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg K.coe_nonneg _)
  have hb2 : MemLp b 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hb.aestronglyMeasurable B (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))
  have hc2 : MemLp c 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hc.aestronglyMeasurable C (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))
  have hu2 : MemLp u 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hu.aestronglyMeasurable U (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hU x))
  have he : (fun x => |b x*u x-c x*u x|) = (fun x => |(b-c) x| * |u x|) := by
    funext x
    rw [←sub_mul,abs_mul]
    rfl
  change (∫ x, |b x*u x-c x*u x| ∂currentMassMeasure h.metric) ≤ _
  rw [he]
  exact integral_abs_mul_le_lpNorm_two (hb2.sub hc2) hu2

noncomputable def projectedL1 (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) : Lp ℝ 1 (volume : Measure (Euc k)) :=
  (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.toL1 _

lemma dist_projectedL1 (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    dist (projectedL1 h hX π hπ hb B hB) (projectedL1 h hX π hπ hc C hC) =
      ∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
        currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j)| := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (projectedL1 h hX π hπ hb B hB) (projectedL1 h hX π hπ hc C hC),
    (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.coeFn_toL1,
    (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hc C hC).1.coeFn_toL1]
    with z hz hzb hzc
  rw [hz]
  change ‖((fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.toL1 _) z-
    ((fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hc C hC).1.toL1 _) z‖ = _
  rw [hzb,hzc,Real.norm_eq_abs]

lemma projectedL1_lipschitz (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : BoundedLip b) {B : ℝ≥0} (hB : ∀ x, |b x| ≤ B) :
    projectedL1 h hX π hπ hb.continuous.measurable B hB =
      (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb
        (fun j => Fin.elim0 j)).toL1 (fun z => fullSlice h π z b (fun j => Fin.elim0 j)) := by
  apply Lp.ext
  filter_upwards [(fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb.continuous.measurable B hB).1.coeFn_toL1,
    (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb (fun j => Fin.elim0 j)).coeFn_toL1]
    with z hz hz'
  exact hz.trans ((currentBorelAction_eq_action (fullSlice_approx h π z).metric ⟨hb,fun j => Fin.elim0 j⟩).trans hz'.symm)

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma coordinate_memLp (i : ℕ) {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0)
    (hU : ∀ x, |u x| ≤ U) (p : ℝ≥0∞) :
    MemLp (fun z => u ((q.chart i).paramExtended z)) p (q.coordinateMeasure i) :=
  MemLp.of_bound (hu.comp (q.chart i).measurable_paramExtended).aestronglyMeasurable U
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hU ((q.chart i).paramExtended z))

noncomputable def coordinateL1 (i : ℕ) {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0)
    (hU : ∀ x, |u x| ≤ U) : Lp ℝ 1 (q.coordinateMeasure i) :=
  (q.coordinate_memLp i hu U hU 1).toLp _

lemma dist_coordinateL1 (i : ℕ) {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV) =
      ∫ z, q.density i z*|u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)|
        ∂volume.restrict (q.chart i).domain := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  have he : (∫ z, ‖(q.coordinateL1 i hu U hU-q.coordinateL1 i hv V hV) z‖ ∂q.coordinateMeasure i) =
      ∫ z, |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| ∂q.coordinateMeasure i := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV),
      (q.coordinate_memLp i hu U hU 1).coeFn_toLp,(q.coordinate_memLp i hv V hV 1).coeFn_toLp] with z hz huz hvz
    rw [hz]
    change ‖((q.coordinate_memLp i hu U hU 1).toLp _) z-((q.coordinate_memLp i hv V hV 1).toLp _) z‖ = _
    rw [huz,hvz,Real.norm_eq_abs]
  rw [he,coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

lemma indicator_bound (i : ℕ) {u : X → ℝ} {U : ℝ≥0} (hU : ∀ x, |u x| ≤ U) :
    ∀ x, |(q.chart i).image.indicator u x| ≤ U := by
  intro x
  by_cases hx : x ∈ (q.chart i).image
  · simpa only [indicator_of_mem hx] using hU x
  · simpa only [indicator_of_notMem hx,abs_zero] using U.coe_nonneg

noncomputable def isolatedL1 (h : NormalApprox n T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    {u : X → ℝ} (hu : Measurable u) (U : ℝ≥0) (hU : ∀ x, |u x| ≤ U) : Lp ℝ 1 (volume : Measure (Euc n)) :=
  projectedL1 h hX F hF (hu.indicator (q.chart i).measurableSet_image) U (q.indicator_bound i hU)

lemma dist_isolatedL1 (h : NormalApprox n T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u v : X → ℝ} {L J : ℝ≥0} (hu : LipschitzWith L u) (hv : LipschitzWith J v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.isolatedL1 h hX i F hF hu.continuous.measurable U hU)
      (q.isolatedL1 h hX i F hF hv.continuous.measurable V hV) =
      ∫ z, |((q.chart i).multiplicity z:ℝ)| * |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)|
        ∂volume.restrict (q.chart i).domain := by
  rw [isolatedL1,isolatedL1,dist_projectedL1]
  rw [←integral_indicator (q.chart i).borel]
  apply integral_congr_ae
  filter_upwards [q.ae_isolated_projected_density h hX i F hF hFinv hjac hu,
    q.ae_isolated_projected_density h hX i F hF hFinv hjac hv] with z huz hvz
  rw [huz,hvz]
  by_cases hz : z ∈ (q.chart i).domain
  · simp only [indicator_of_mem hz,←mul_sub,abs_mul]
  · simp only [indicator_of_notMem hz,sub_self,abs_zero]

end CAT0Fillings.ChartGeometry
end

end OAI
