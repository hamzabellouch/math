import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.Coordinates
import OAI.Geometry.CAT0Fillings.Gradient.Determinant

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators MatrixOrder

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def testWeight (π : Fin k → X → ℝ) (L : ℕ × Euc (k+1) → Euc (k+1))
    (w : ℕ × Euc (k+1)) : ℝ :=
  let a : ℝ := (q.chart w.1).multiplicity w.2
  (a/abs a)*normalizedDet (q.gram w.1 w.2) (fun j => q.covector w.1 (π j) w.2) (L w)

lemma aestronglyMeasurable_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : AEStronglyMeasurable L q.atlasMeasure) :
    AEStronglyMeasurable (q.testWeight π L) q.atlasMeasure := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
  have hLi := (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mp
    (aestronglyMeasurable_sum_measure_iff.mp hL i)
  have ha := (q.chart i).integrable.aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict (q.chart i).domain)
      (fun z => ENNReal.ofReal (q.density i z)))
  have hR : AEStronglyMeasurable (fun z j => q.covector i (π j) z) (q.coordinateMeasure i) := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.of_eval (fun j =>
      ((q.aestronglyMeasurable_covector i (hπ j)).mono_ac
        (withDensity_absolutelyContinuous _ _)).aemeasurable)
  exact ((ha.aemeasurable.div ha.aemeasurable.abs).aestronglyMeasurable).mul
    (aestronglyMeasurable_normalizedDet _ (q.measurable_gram i) hR hLi)

lemma ae_testWeight_bound (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) (L : ℕ × Euc (k+1) → Euc (k+1)) :
    ∀ᵐ w ∂q.atlasMeasure, |q.testWeight π L w| ≤ ‖L w‖ * ∏ j, (K j : ℝ) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  have hR : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ∀ j, q.duNorm i (π j) z ≤ K j := by
    rw [eventually_all]
    intro j
    exact (q.ae_duNorm_bounds i (hπ j)).mono (fun z hz => hz.2.1)
  filter_upwards [q.differential i,hR] with z hz hRz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  change abs ((_ / abs _) * normalizedDet _ _ _) ≤ _
  rw [abs_mul]
  have hh := normalizedDet_bound_prod (q.gram i z) hG
    (fun j => q.covector i (π j) z) K hRz (L (i,z))
  exact (mul_le_mul_of_nonneg_right (orientation_bound _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using hh)

lemma memLp_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) : MemLp (q.testWeight π L) 2 q.atlasMeasure := by
  apply (hL.norm.mul_const (∏ j, (K j : ℝ))).mono'
    (q.aestronglyMeasurable_testWeight π K hπ hL.aestronglyMeasurable)
  simpa only [Real.norm_eq_abs] using q.ae_testWeight_bound π K hπ L

lemma testWeight_sub (π : Fin k → X → ℝ) (L M : ℕ × Euc (k+1) → Euc (k+1)) :
    q.testWeight π (L-M) = q.testWeight π L-q.testWeight π M := by
  funext w
  simp only [testWeight,Pi.sub_apply,normalizedDet_sub,mul_sub]

lemma integrable_testWeight_mul (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun w => q.testWeight π L w*b (q.atlasParam w)) q.atlasMeasure := by
  obtain ⟨Kb,hbK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  have hm : MemLp (fun w => b (q.atlasParam w)) 2 q.atlasMeasure :=
    MemLp.of_bound (hbK.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable M
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hM (q.atlasParam w))
  exact (q.memLp_testWeight π K hπ hL).integrable_mul hm

lemma testWeight_gradient (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {u b : X → ℝ} {Ku : ℝ≥0}
    (hu : LipschitzWith Ku u) (hb : BoundedLip b) :
    (∫ w, q.testWeight π (q.gradientFunction u) w*b (q.atlasParam w) ∂q.atlasMeasure) =
      T b (Fin.cons u π) := by
  have hi := q.integrable_testWeight_mul π K hπ (q.memLp_gradientFunction hu) hb
  rw [atlasMeasure,integral_sum_measure hi,q.action]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have ha : Admissible b (Fin.cons u π) := Foundations.admissible_vecCons hb
    ⟨Ku,hu⟩ (fun j => ⟨K j,hπ j⟩)
  rw [IntegerChart.action,ite_eq_left ha]
  apply integral_congr_ae
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel] with z hz hzi
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i z),smul_eq_mul,
    testWeight,gradientFunction,normalizedDet,normalizedCovector,raw_normalizedCovector _ hG]
  have hd : Matrix.det (Matrix.vecCons (q.covector i u z) (fun j => q.covector i (π j) z)) =
      (q.chart i).jacobian (Fin.cons u π) z := by
    congr 1
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> rfl
  rw [hd]
  have hbz : b (q.atlasParam (i,z)) = (q.chart i).scalar b z := by
    simp only [atlasParam,IntegerChart.paramExtended,IntegerChart.scalar,dite_eq_left hzi]
  rw [hbz]
  unfold density
  have ho := orientation_density ((q.chart i).multiplicity z : ℝ)
  have hJ : Real.sqrt (q.gram i z).det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  calc
    _ = (abs ((q.chart i).multiplicity z : ℝ)*
        (((q.chart i).multiplicity z : ℝ)/abs ((q.chart i).multiplicity z : ℝ)))*
        (q.chart i).jacobian (Fin.cons u π) z*(q.chart i).scalar b z := by field_simp [hJ]
    _ = _ := by rw [ho]; ring

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma integral_norm_le_lpNorm_two {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f 2 μ * Real.sqrt (μ.real univ) := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hf.norm)
    (show MemLp (fun _ : α => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simpa only [norm_one,mul_one,Real.one_rpow,integral_const,smul_eq_mul,
    mul_one,ENNReal.toReal_ofNat,one_div,Real.sqrt_eq_rpow,norm_norm] using hh

lemma lpNorm_Lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (f : Lp E p μ) : lpNorm f p μ = ‖f‖ := by
  rw [Lp.norm_def,toReal_eLpNorm]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def pairing (π : Fin k → X → ℝ) (b : X → ℝ)
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure) : ℝ :=
  ∫ w, q.testWeight π L w*b (q.atlasParam w) ∂q.atlasMeasure

lemma pairing_sub (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b)
    (L M : Lp (Euc (k+1)) 2 q.atlasMeasure) :
    q.pairing π b (L-M) = q.pairing π b L-q.pairing π b M := by
  calc
    _ = ∫ w, (q.testWeight π L w-q.testWeight π M w)*b (q.atlasParam w)
        ∂q.atlasMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub L M] with w hw
      simp only [testWeight] at *
      rw [hw]
      simp only [Pi.sub_apply,normalizedDet_sub,mul_sub]
    _ = _ := by
      simp only [sub_mul]
      rw [integral_sub (q.integrable_testWeight_mul π K hπ (Lp.memLp L) hb)
        (q.integrable_testWeight_mul π K hπ (Lp.memLp M) hb)]
      rfl

lemma abs_pairing_le (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x, |b x| ≤ B)
    (L : Lp (Euc (k+1)) 2 q.atlasMeasure) :
    |q.pairing π b L| ≤ ((∏ j, (K j : ℝ))*B*Real.sqrt (q.atlasMeasure.real univ))*‖L‖ := by
  have hi : Integrable (fun w => ‖L w‖*((∏ j, (K j : ℝ))*B)) q.atlasMeasure :=
    ((Lp.memLp L).integrable (by norm_num)).norm.mul_const _
  have hbound : ∀ᵐ w ∂q.atlasMeasure,
      ‖q.testWeight π L w*b (q.atlasParam w)‖ ≤ ‖L w‖*((∏ j, (K j : ℝ))*B) := by
    filter_upwards [q.ae_testWeight_bound π K hπ L] with w hw
    rw [Real.norm_eq_abs,abs_mul]
    have hh := mul_le_mul hw (hbB (q.atlasParam w)) (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _ => (K j).coe_nonneg))
    exact hh.trans_eq (by ring)
  have hh := (norm_integral_le_integral_norm
    (fun w => q.testWeight π L w*b (q.atlasParam w))).trans
      (integral_mono_ae
        (q.integrable_testWeight_mul π K hπ (Lp.memLp L) hb).norm hi hbound)
  change |q.pairing π b L| ≤ _ at hh
  rw [integral_mul_const] at hh
  have hc := mul_le_mul_of_nonneg_right (integral_norm_le_lpNorm_two (Lp.memLp L))
    (show 0 ≤ (∏ j, (K j : ℝ))*B from mul_nonneg (Finset.prod_nonneg fun j _ => (K j).coe_nonneg) hB)
  rw [lpNorm_Lp] at hc
  exact (hh.trans hc).trans_eq (by ring)

lemma continuous_pairing (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {b : X → ℝ} (hb : BoundedLip b) :
    Continuous (q.pairing π b) := by
  obtain ⟨B,hB⟩ := hb.2
  have hB0 : 0 ≤ B := (abs_nonneg (b (Classical.arbitrary X))).trans (hB _)
  let C : ℝ≥0 := ⟨(∏ j, (K j : ℝ))*B*Real.sqrt (q.atlasMeasure.real univ),by positivity⟩
  apply LipschitzWith.continuous (K := C)
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro L M
  rw [Real.dist_eq,←q.pairing_sub π K hπ hb,dist_eq_norm]
  exact q.abs_pairing_le π K hπ hb hB0 hB (L-M)

lemma pairing_gradient (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {u b : X → ℝ} {Ku : ℝ≥0}
    (hu : LipschitzWith Ku u) (hb : BoundedLip b) :
    q.pairing π b (q.gradient hu) = T b (Fin.cons u π) := by
  rw [←q.testWeight_gradient π K hπ hu hb]
  apply integral_congr_ae
  filter_upwards [(q.memLp_gradientFunction hu).coeFn_toLp] with w hw
  simp only [gradient,testWeight]
  rw [hw]

end ChartGeometry
end CAT0Fillings
end

end OAI
