import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Gradient.Chart
import OAI.Geometry.CAT0Fillings.Fillings.WeightedCone

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def weightedMeasure (v : ℕ → Euc k → ℝ) : Measure X :=
  Measure.sum (fun i => densityPush (volume.restrict (q.chart i).domain)
    (q.chart i).paramExtended (fun z => q.density i z * v i z))

lemma weightedMeasure_le {v : ℕ → Euc k → ℝ} {c : ℝ≥0}
    (hv : ∀ i, ∀ᵐ z ∂volume.restrict (q.chart i).domain, v i z ≤ c) :
    q.weightedMeasure v ≤ c • MassMeasure.currentMassMeasure hT := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedMeasure,Measure.sum_apply _ hs,Measure.smul_apply,q.measure_eq,
    Measure.sum_apply _ hs]
  change _ ≤ (c : ℝ≥0∞) * _
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  have hi := densityPush_mono_ae (q.chart i).measurable_paramExtended
    ((hv i).mono fun z hz => (mul_le_mul_of_nonneg_left hz (q.density_nonneg i z)).trans_eq
      (mul_comm _ _))
  rw [densityPush_const_mul _ _ _ _ (q.chart i).measurable_paramExtended] at hi
  exact hi s

lemma weightedMeasure_finite {v : ℕ → Euc k → ℝ} {c : ℝ≥0}
    (hv : ∀ i, ∀ᵐ z ∂volume.restrict (q.chart i).domain, v i z ≤ c) :
    IsFiniteMeasure (q.weightedMeasure v) :=
  isFiniteMeasure_of_le (c • MassMeasure.currentMassMeasure hT) (q.weightedMeasure_le hv)

noncomputable def gradientMeasure (u : X → ℝ) : Measure X :=
  q.weightedMeasure (fun i => q.duNorm i u)
noncomputable def energyMeasure (u : X → ℝ) : Measure X :=
  q.weightedMeasure (fun i => q.normSq i u)

lemma gradientMeasure_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.gradientMeasure u ≤ K • MassMeasure.currentMassMeasure hT :=
  q.weightedMeasure_le (fun i => (q.ae_duNorm_bounds i hu).mono fun _ hz => hz.2.1)

lemma energyMeasure_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.energyMeasure u ≤ K^2 • MassMeasure.currentMassMeasure hT := by
  apply q.weightedMeasure_le
  intro i
  simpa only [NNReal.coe_pow] using (q.ae_normSq_bounds i hu).mono (fun _ hz => hz.2)

lemma gradientMeasure_finite {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    IsFiniteMeasure (q.gradientMeasure u) :=
  isFiniteMeasure_of_le _ (q.gradientMeasure_le hu)

lemma energyMeasure_finite {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    IsFiniteMeasure (q.energyMeasure u) :=
  isFiniteMeasure_of_le _ (q.energyMeasure_le hu)

lemma integral_gradientMeasure {u w : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hw : Continuous w) :
    (∫ x, w x ∂q.gradientMeasure u) = ∑' i, ∫ z,
      (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain := by
  let := q.gradientMeasure_finite hu
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := q.gradientMeasure u)
  rw [gradientMeasure,weightedMeasure] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_gradient i hu)
    (Eventually.of_forall fun z => mul_nonneg (q.density_nonneg i z) (Real.sqrt_nonneg _)) hw

lemma gradient_summable {u w : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hw : Continuous w) :
    Summable (fun i => ∫ z,
      (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) := by
  let := q.gradientMeasure_finite hu
  have hi := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)
    (μ := q.gradientMeasure u)
  apply (hasSum_integral_measure hi).summable.congr
  intro i
  exact integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_gradient i hu)
    (Eventually.of_forall fun z => mul_nonneg (q.density_nonneg i z) (Real.sqrt_nonneg _)) hw

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

local instance {n : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma matrix_posSemidef_closed {n : ℕ} :
    IsClosed {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · change IsClosed {P : Matrix (Fin n) (Fin n) ℝ | P.conjTranspose = P}
    exact isClosed_eq (by fun_prop) continuous_id
  · have hh (v : Fin n → ℝ) : IsClosed {P : Matrix (Fin n) (Fin n) ℝ |
        0 ≤ star v ⬝ᵥ P.mulVec v} := isClosed_le continuous_const (by fun_prop)
    have hs : {P : Matrix (Fin n) (Fin n) ℝ | ∀ v, 0 ≤ star v ⬝ᵥ P.mulVec v} =
        ⋂ v, {P : Matrix (Fin n) (Fin n) ℝ | 0 ≤ star v ⬝ᵥ P.mulVec v} := by
      ext P
      simp only [mem_iInter,mem_ofPred_eq]
    change IsClosed {P : Matrix (Fin n) (Fin n) ℝ | ∀ v, 0 ≤ star v ⬝ᵥ P.mulVec v}
    rw [hs]
    exact isClosed_iInter hh

lemma measurable_matrix_sqrt {n : ℕ} :
    Measurable (CFC.sqrt : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  classical
  have hm : MeasurableSet {P : Matrix (Fin n) (Fin n) ℝ | 0 ≤ P} := by
    simpa only [Matrix.nonneg_iff_posSemidef] using (matrix_posSemidef_closed (n := n)).measurableSet
  have h := (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ)).measurable_piecewise
    (g := fun _ => 0) continuousOn_const hm
  convert h using 1
  funext P
  by_cases hp : 0 ≤ P
  · simp only [Set.piecewise,mem_ofPred_eq,hp,ite_true]
  · simp only [Set.piecewise,mem_ofPred_eq,hp,ite_false,CFC.sqrt_of_not_nonneg hp]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def normalizedCovector (i : ℕ) (u : X → ℝ) (z : Euc n) : Euc n :=
  WithLp.toLp 2 ((CFC.sqrt (q.gram i z)⁻¹).mulVec (q.covector i u z))

lemma aestronglyMeasurable_normalizedCovector (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.normalizedCovector i u)
      (volume.restrict (q.chart i).domain) := by
  have hM := measurable_matrix_sqrt.comp (measurable_matrix_inverse _ (q.measurable_gram i))
  have hc : Continuous (fun r : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
    (WithLp.toLp 2 (r.1.mulVec r.2) : Euc n)) := by fun_prop
  exact hc.comp_aestronglyMeasurable
    (hM.aestronglyMeasurable.prodMk (q.aestronglyMeasurable_covector i hu))

lemma ae_normalizedCovector_norm_sq (i : ℕ) (u : X → ℝ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ‖q.normalizedCovector i u z‖^2 = q.normSq i u z := by
  filter_upwards [q.differential i] with z hz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  rw [←real_inner_self_eq_norm_sq]
  simp only [normalizedCovector,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  exact (dot_mulVec_sqrt _ hG.inv.posSemidef _).symm

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def coordinateMeasure (i : ℕ) : Measure (Euc n) :=
  (volume.restrict (q.chart i).domain).withDensity (fun z => ENNReal.ofReal (q.density i z))
noncomputable def atlasMeasure : Measure (ℕ × Euc n) :=
  Measure.sum (fun i => (q.coordinateMeasure i).map (Prod.mk i))

instance coordinateMeasure_finite (i : ℕ) : IsFiniteMeasure (q.coordinateMeasure i) :=
  isFiniteMeasure_withDensity_ofReal (q.density_integrable i).hasFiniteIntegral

lemma coordinateMeasure_total (i : ℕ) : (q.coordinateMeasure i).real univ =
    ∫ z, q.density i z ∂volume.restrict (q.chart i).domain := by
  rw [show (q.coordinateMeasure i).real univ = ∫ _ : Euc n, (1:ℝ) ∂q.coordinateMeasure i by simp]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul,mul_one]

instance atlasMeasure_finite : IsFiniteMeasure q.atlasMeasure := by
  apply finite_sum_measure_of_summable_total
  apply q.density_summable.congr
  intro i
  rw [←q.coordinateMeasure_total]
  simp only [measureReal_def,Measure.map_apply measurable_prodMk_left MeasurableSet.univ,preimage_univ]

noncomputable def gradientFunction (u : X → ℝ) (w : ℕ × Euc n) : Euc n :=
  q.normalizedCovector w.1 u w.2

lemma aestronglyMeasurable_gradientFunction {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.gradientFunction u) q.atlasMeasure := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
  exact (q.aestronglyMeasurable_normalizedCovector i hu).mono_ac
    (withDensity_absolutelyContinuous _ _)

lemma ae_gradientFunction_bound {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ w ∂q.atlasMeasure, ‖q.gradientFunction u w‖ ≤ K := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [q.ae_normalizedCovector_norm_sq i u,q.ae_normSq_bounds i hu] with z hz hb
  change ‖q.normalizedCovector i u z‖ ≤ K
  nlinarith [norm_nonneg (q.normalizedCovector i u z),K.coe_nonneg]

lemma memLp_gradientFunction {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    MemLp (q.gradientFunction u) 2 q.atlasMeasure :=
  MemLp.of_bound (q.aestronglyMeasurable_gradientFunction hu) K (q.ae_gradientFunction_bound hu)

noncomputable def gradient {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Lp (Euc n) 2 q.atlasMeasure := (q.memLp_gradientFunction hu).toLp _

lemma gradient_norm_sq {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖q.gradient hu‖^2 = (q.energyMeasure u).real univ := by
  have hi : Integrable (fun w => ‖q.gradientFunction u w‖^2) q.atlasMeasure := by
    exact (q.memLp_gradientFunction hu).integrable_norm_pow (by norm_num)
  have hleft : ‖q.gradient hu‖^2 = ∫ w, ‖q.gradientFunction u w‖^2 ∂q.atlasMeasure := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(q.memLp_gradientFunction hu).coeFn_toLp] with w hw
    rw [gradient,hw,real_inner_self_eq_norm_sq]
  have he : (q.energyMeasure u).real univ = ∑' i, ∫ z,
      q.density i z*q.normSq i u z ∂volume.restrict (q.chart i).domain := by
    let := q.energyMeasure_finite hu
    rw [show (q.energyMeasure u).real univ = ∫ _ : X, (1:ℝ) ∂q.energyMeasure u by simp]
    have hI : Integrable (fun _ : X => (1:ℝ)) (q.energyMeasure u) := integrable_const _
    rw [energyMeasure,weightedMeasure] at hI ⊢
    rw [integral_sum_measure hI]
    apply tsum_congr
    intro i
    rw [integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_energy i hu)
      ((q.ae_normSq_bounds i hu).mono fun z hz => mul_nonneg (q.density_nonneg i z) hz.1) continuous_const]
    simp only [mul_one]
  rw [hleft,atlasMeasure,integral_sum_measure hi,he]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [q.ae_normalizedCovector_norm_sq i u] with z hz
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i z),smul_eq_mul,gradientFunction, hz]

end CAT0Fillings.ChartGeometry
end

end OAI
