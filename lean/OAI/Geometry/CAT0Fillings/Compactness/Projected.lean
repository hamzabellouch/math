import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Compactness.BV
import OAI.Geometry.CAT0Fillings.Compactness.IntrinsicBV

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_mul {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.gradientFunction (fun x => u x*v x) =ᵐ[q.atlasMeasure]
      fun w => u (q.atlasParam w) • q.gradientFunction v w+
        v (q.atlasParam w) • q.gradientFunction u w := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [(q.chart i).ae_fderivWithin_scalar_mul hu hv,
    ae_restrict_mem (q.chart i).borel] with z hz hzi
  change q.normalizedCovector i (fun x => u x*v x) z = _
  unfold normalizedCovector covector
  rw [hz]
  have hr (L M : Euc (k+1) →L[ℝ] ℝ) (a b : ℝ) :
      differentialRow (a • L+b • M) = a • differentialRow L+b • differentialRow M := rfl
  rw [hr,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,WithLp.toLp_add,
    WithLp.toLp_smul,WithLp.toLp_smul]
  simp only [gradientFunction,normalizedCovector,covector,atlasParam,
    IntegerChart.paramExtended,IntegerChart.scalar,dite_eq_left hzi]

lemma integral_gradientFunction_norm {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    (∫ w, ‖q.gradientFunction u w‖ ∂q.atlasMeasure) ≤
      ‖q.gradient hu‖*Real.sqrt (q.atlasMeasure.real univ) := by
  have hh := integral_norm_le_lpNorm_two (q.memLp_gradientFunction hu)
  have hn : lpNorm (q.gradientFunction u) 2 q.atlasMeasure = ‖q.gradient hu‖ := by
    rw [gradient,Lp.norm_toLp,toReal_eLpNorm]
  rwa [hn] at hh

lemma integral_gradient_mul_bound {u χ : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hχ : LipschitzWith J χ) {B : ℝ}
    (hB : 0 ≤ B) (hχB : ∀ x, |χ x| ≤ B) :
    (∫ w, ‖q.gradientFunction (fun x => χ x*u x) w‖ ∂q.atlasMeasure) ≤
      B*‖q.gradient hu‖*Real.sqrt (q.atlasMeasure.real univ)+
        J*‖value (hT := hT) hu‖*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ) := by
  let μ := MassMeasure.currentMassMeasure hT
  have hχb := Foundations.boundedLip_of_lipschitz hχ
  have hub := Foundations.boundedLip_of_lipschitz hu
  obtain ⟨M,hm⟩ := (hχb.mul hub).1
  have hia := ((q.memLp_gradientFunction hu).integrable (by norm_num)).norm.const_mul B
  have hiu : Integrable (fun w => |u (q.atlasParam w)|) q.atlasMeasure := by
    have hh : Integrable (fun x => |u x|) (q.atlasMeasure.map q.atlasParam) := by
      rw [q.map_atlasMeasure]
      exact ((hub.memLp 2).integrable (by norm_num)).abs
    exact (integrable_map_measure (hu.continuous.abs.aestronglyMeasurable)
      q.measurable_atlasParam.aemeasurable).mp hh
  have hib := hiu.const_mul (J:ℝ)
  have hpoint : ∀ᵐ w ∂q.atlasMeasure,
      ‖q.gradientFunction (fun x => χ x*u x) w‖ ≤
        B*‖q.gradientFunction u w‖+J*|u (q.atlasParam w)| := by
    filter_upwards [q.gradientFunction_mul hχ hu,q.ae_gradientFunction_bound hχ] with w hw hwb
    rw [hw]
    calc _ ≤ ‖χ (q.atlasParam w) • q.gradientFunction u w‖+
          ‖u (q.atlasParam w) • q.gradientFunction χ w‖ := norm_add_le _ _
      _ ≤ B*‖q.gradientFunction u w‖+J*|u (q.atlasParam w)| := by
        simp only [norm_smul,Real.norm_eq_abs]
        exact add_le_add (mul_le_mul_of_nonneg_right (hχB _) (norm_nonneg _))
          ((mul_le_mul_of_nonneg_left hwb (abs_nonneg _)).trans_eq (mul_comm _ _))
  have hh := integral_mono_ae ((q.memLp_gradientFunction hm).integrable (by norm_num)).norm
    (hia.add hib) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hia hib,integral_const_mul,integral_const_mul] at hh
  have he : (∫ w, |u (q.atlasParam w)| ∂q.atlasMeasure) = ∫ x, |u x| ∂μ := by
    dsimp only [μ]
    rw [←q.map_atlasMeasure,integral_map q.measurable_atlasParam.aemeasurable
      hu.continuous.abs.aestronglyMeasurable]
  rw [he] at hh
  have huL := integral_norm_le_lpNorm_two (hub.memLp (μ := μ) 2)
  rw [←norm_value (hT := hT) hu] at huL
  simp only [Real.norm_eq_abs] at huL
  exact hh.trans (by
    have h1 := mul_le_mul_of_nonneg_left (q.integral_gradientFunction_norm hu) hB
    have h2 := mul_le_mul_of_nonneg_left huL J.coe_nonneg
    nlinarith)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma intrinsicSliceControl_total (π : Fin (k+1) → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) {u : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) :
    (q.intrinsicSliceControl π K u).real univ =
      (K:ℝ)^k*∫ w, ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  simpa using q.intrinsicSliceControl_integral π hπ hu (φ := fun _ => (1:ℝ)) continuous_const

lemma fullSlice_L1_bound {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    (∫ z, |fullSlice h π z u (fun j => Fin.elim0 j)|) ≤
      (K:ℝ)^(k+1)*∫ x, |u x| ∂currentMassMeasure hT := by
  obtain ⟨B,hB⟩ := (boundedLip_of_lipschitz hu).2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hh := fullSlice_borel_L1_bound h hX π hπ hu.continuous.measurable B'
    (fun x => (hB x).trans (le_max_left _ _))
  simpa only [currentBorelAction_eq_action (fullSlice_approx h π _).metric
    ⟨boundedLip_of_lipschitz hu,fun j => Fin.elim0 j⟩] using hh

theorem totallyBounded_whole_projected {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    (u : ι → X → ℝ) (L : ι → ℝ≥0) (hu : ∀ i, LipschitzWith (L i) (u i))
    {χ : X → ℝ} {J : ℝ≥0} (hχ : LipschitzWith J χ)
    (M : ℝ≥0) (hMv : ∀ i, ‖value (hT := hT) (hu i)‖ ≤ M)
    (hMg : ∀ i, ‖q.gradient (hu i)‖ ≤ M) :
    TotallyBounded (range fun i =>
      (fullSlice_eval_integrable h hX π (fun a => boundedLip_of_lipschitz (hπ a))
        ((boundedLip_of_lipschitz hχ).mul (boundedLip_of_lipschitz (hu i)))
          (fun j => Fin.elim0 j)).toL1
      (fun z => fullSlice h π z (fun x => χ x*u i x) (fun j => Fin.elim0 j))) := by
  obtain ⟨B₀,hB₀⟩ := (boundedLip_of_lipschitz hχ).2
  let B : ℝ≥0 := ⟨max B₀ 0,le_max_right _ _⟩
  have hB x : |χ x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  let v i := fun x => χ x*u i x
  have hvb i : BoundedLip (v i) := (boundedLip_of_lipschitz hχ).mul (boundedLip_of_lipschitz (hu i))
  choose N hv using fun i => (hvb i).1
  let f i := fun z => fullSlice h π z (v i) (fun j => Fin.elim0 j)
  have hfi i : Integrable (f i) := fullSlice_eval_integrable h hX π
    (fun a => boundedLip_of_lipschitz (hπ a)) (hvb i) _
  let ν i := q.intrinsicSliceControl π K (v i)
  have : ∀ index, IsFiniteMeasure (ν index) :=
    fun index => q.intrinsicSliceControl_finite π K (hv index)
  let m := Real.sqrt ((currentMassMeasure hT).real univ)
  let a := Real.sqrt (q.atlasMeasure.real univ)
  let C : ℝ≥0 := ⟨(K:ℝ)^k*(B*M*a+J*M*m),by dsimp [a,m]; positivity⟩
  let D : ℝ≥0 := ⟨(K:ℝ)^(k+1)*B*M*m,by dsimp [m]; positivity⟩
  obtain ⟨K',hK'⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨R,hR⟩ := (isCompact_range hK'.continuous).isBounded.subset_closedBall (0:Euc (k+1))
  apply totallyBounded_L1_of_directional_variation f hfi ν
    (fun i l => q.fullSlice_intrinsic_directional_variation h hz hX π hπ (hv i) l) D ?_ C ?_ R ?_
  · intro i
    apply (fullSlice_L1_bound (hv i) h hX π hπ).trans
    have hint : (∫ x, |v i x| ∂currentMassMeasure hT) ≤
        B*∫ x, |u i x| ∂currentMassMeasure hT := by
      rw [←integral_const_mul]
      apply integral_mono (integrable_boundedLip _ (hvb i)).abs
        ((integrable_boundedLip _ (boundedLip_of_lipschitz (hu i))).abs.const_mul B)
      intro x
      exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    have hil := integral_norm_le_lpNorm_two ((boundedLip_of_lipschitz (hu i)).memLp (μ := currentMassMeasure hT) 2)
    rw [←norm_value (hT := hT) (hu i)] at hil
    simp only [Real.norm_eq_abs] at hil
    have him : (∫ x, |u i x| ∂currentMassMeasure hT) ≤ M*m :=
      hil.trans (mul_le_mul_of_nonneg_right (hMv i) (Real.sqrt_nonneg _))
    change _ ≤ (K:ℝ)^(k+1)*B*M*m
    nlinarith [pow_nonneg K.coe_nonneg (k+1),mul_le_mul_of_nonneg_left hint (pow_nonneg K.coe_nonneg (k+1)),
      mul_le_mul_of_nonneg_left him (mul_nonneg (pow_nonneg K.coe_nonneg (k+1)) B.coe_nonneg)]
  · intro i
    rw [intrinsicSliceControl_total q π hπ (hv i)]
    apply (mul_le_mul_of_nonneg_left (q.integral_gradient_mul_bound (hu i) hχ B.coe_nonneg hB)
      (pow_nonneg K.coe_nonneg k)).trans
    change _ ≤ (K:ℝ)^k*(B*M*a+J*M*m)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg K.coe_nonneg k)
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMg i) B.coe_nonneg) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMv i) J.coe_nonneg) (Real.sqrt_nonneg _))
  · intro i
    obtain ⟨B',hB'⟩ := (hvb i).2
    let B'' : ℝ≥0 := ⟨max B' 0,le_max_right _ _⟩
    have hs := ae_fullSlice_borel_support h hX π (fun a => boundedLip_of_lipschitz (hπ a))
      (hv i).continuous.measurable B'' (fun x => (hB' x).trans (le_max_left _ _))
    filter_upwards [hs] with z hz
    intro hnot
    have hh := hz (fun hh => hnot (hR hh))
    simpa only [currentBorelAction_eq_action (fullSlice_approx h π z).metric
      ⟨hvb i,fun j => Fin.elim0 j⟩] using hh

end CAT0Fillings.ChartGeometry
end

end OAI
