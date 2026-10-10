import OAI.Probability.GaussianReplacement.FiberGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma prod_cubeKernel_scaled {k : ℕ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (z : Fin k→ℝ) :
    (∏ i, cubeKernel δ (r*z i)) =
      (Metric.closedBall (0:Fin k→ℝ) (δ/r)).indicator
        (fun _ => ENNReal.ofReal ((2*δ)⁻¹ ^ k)) z := by
  classical
  have hz : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/r) ↔ ∀ i, r*z i ∈ Icc (-δ) δ := by
    rw [Metric.mem_closedBall,dist_pi_le_iff (div_nonneg hδ.le hr.le)]
    simp only [Pi.zero_apply,dist_zero_right,Real.norm_eq_abs,mem_Icc,←abs_le]
    exact forall_congr' (fun i => by rw [abs_mul,abs_of_pos hr,le_div_iff₀ hr,mul_comm])
  by_cases h : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/r)
  · rw [indicator_of_mem h]
    simp only [cubeKernel,indicator_of_mem (hz.mp h _),Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,ENNReal.ofReal_pow (by positivity : (0:ℝ)≤(2*δ)⁻¹)]
  · rw [indicator_of_notMem h]
    have hh := mt hz.mpr h
    push Not at hh
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)

section SlabLimit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma normalized_direction {v : E} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma gaussian_slab_formula {k : ℕ} {v : E} (hv : v ≠ 0)
    (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ C : Fin k→E, (H C : ℝ≥0∞)*(∏ i, cubeKernel δ ⟪v,C i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) =
    ENNReal.ofReal ((2*δ)⁻¹ ^ k) *
      ∫⁻ z in Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖),
        ENNReal.ofReal (gaussianProductPDF 1 0 z) *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct (‖v‖⁻¹ • v) (z,G)) : ℝ≥0∞)
            ∂Measure.pi (fun _ => stdGaussian E) := by
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := normalized_direction hv
  have hvu : v = ‖v‖ • u := by
    dsimp [u]
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  have hpair (zG : (Fin k→ℝ)×(Fin k→E)) (i : Fin k) :
      ⟪v,gaussianReconstruct u zG i⟫ = ‖v‖*zG.1 i := by
    conv_lhs => rw [hvu]
    rw [inner_smul_left,conj_trivial,gaussian_reconstruct_pairing hu]
  have hK := measurable_cubeKernel δ
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  calc
    _ = ∫⁻ zG : (Fin k→ℝ)×(Fin k→E),
        (H (gaussianReconstruct u zG) : ℝ≥0∞) *
          ∏ i, cubeKernel δ (‖v‖*zG.1 i)
        ∂(gaussianLabels k).prod (Measure.pi (fun _ => stdGaussian E)) := by
      conv_lhs => rw [←gaussian_reconstruct_law hu k]
      rw [lintegral_map (by fun_prop) (by unfold gaussianReconstruct; fun_prop)]
      simp_rw [hpair]
      rfl
    _ = ∫⁻ z : Fin k→ℝ, (∏ i, cubeKernel δ (‖v‖*z i)) *
        ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)
          ∂Measure.pi (fun _ => stdGaussian E) ∂gaussianLabels k := by
      rw [lintegral_prod _ (by unfold gaussianReconstruct; fun_prop)]
      congr 1
      funext z
      simp only
      have hHz : Measurable (fun G : Fin k→E => (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)) :=
        hH.comp (by unfold gaussianReconstruct; fun_prop)
      rw [lintegral_mul_const _ hHz,mul_comm]
    _ = _ := by
      have hp : Measurable (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z)) := by
        unfold gaussianProductPDF
        fun_prop
      have hs : Measurable (fun z : Fin k→ℝ => ∫⁻ G : Fin k→E,
          (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E)) :=
        (continuous_gaussian_slice H).measurable
      rw [←gaussianLabels_density,lintegral_withDensity_eq_lintegral_mul₀ hp.aemeasurable
        (show Measurable (fun z : Fin k→ℝ => (∏ i, cubeKernel δ (‖v‖*z i)) *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞)
            ∂Measure.pi (fun _ => stdGaussian E)) from
          (by exact (by fun_prop : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (‖v‖*z i))).mul hs)).aemeasurable]
      simp only [Pi.mul_apply]
      simp_rw [prod_cubeKernel_scaled (norm_pos_iff.mpr hv) hδ]
      rw [show (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z) *
          ((Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖)).indicator (fun _ => ENNReal.ofReal ((2*δ)⁻¹^k)) z *
          ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E))) =
        (Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖)).indicator
          (fun z => ENNReal.ofReal ((2*δ)⁻¹^k) *
            (ENNReal.ofReal (gaussianProductPDF 1 0 z) *
            ∫⁻ G : Fin k→E, (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E))) by
        funext z
        by_cases hz : z ∈ Metric.closedBall (0:Fin k→ℝ) (δ/‖v‖) <;> simp [hz,mul_left_comm]]
      rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma gaussian_slab_limit {k : ℕ} {v : E} (hv : v ≠ 0)
    (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) :
    Tendsto (fun δ : ℝ => ∫⁻ C : Fin k→E, (H C : ℝ≥0∞)*(∏ i, cubeKernel δ ⟪v,C i⟫)
      ∂Measure.pi (fun _ => stdGaussian E)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (‖v‖⁻¹ ^ k) *
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹ ^ k) *
        ∫⁻ G : Fin k→E, (H (fun i => directionComplement (‖v‖⁻¹ • v) (G i)) : ℝ≥0∞)
          ∂Measure.pi (fun _ => stdGaussian E)))) := by
  have hF : Continuous (fun z : Fin k→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 z) *
      ∫⁻ G : Fin k→E, (H (gaussianReconstruct (‖v‖⁻¹ • v) (z,G)) : ℝ≥0∞)
        ∂Measure.pi (fun _ => stdGaussian E)) := by
    apply Continuous.ennreal_mul
    · apply ENNReal.continuous_ofReal.comp
      unfold gaussianProductPDF gaussianPDFReal
      fun_prop
    · exact continuous_gaussian_slice H
    · intro z
      left
      exact ENNReal.ofReal_pos.mpr (by
        unfold gaussianProductPDF
        apply Finset.prod_pos
        intro i _
        apply gaussianPDFReal_pos
        exact radiusVariance_ne_zero (by norm_num)) |>.ne'
    · intro z
      exact Or.inr ENNReal.ofReal_ne_top
  have ht := tendsto_scaled_cube_average _ hF.continuousAt (norm_pos_iff.mpr hv)
  have hzero : gaussianProductPDF (k:=k) 1 0 0 = (Real.sqrt (2*Real.pi))⁻¹ ^ k := by
    simp only [gaussianProductPDF,gaussianPDFReal,radiusVariance,Pi.zero_apply,
      one_pow,sub_zero,zero_pow (by norm_num : 2 ≠ 0),neg_zero,
      zero_div,Real.exp_zero,mul_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    change (Real.sqrt (2*Real.pi*1))⁻¹ ^ k = _
    rw [mul_one]
  rw [hzero] at ht
  have hz (G : Fin k→E) : gaussianReconstruct (‖v‖⁻¹ • v) ((0:Fin k→ℝ), G) =
      (fun i => directionComplement (‖v‖⁻¹ • v) (G i)) := by
    funext i
    simp [gaussianReconstruct]
  simp_rw [hz] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (gaussian_slab_formula hv H hδ).symm
end SlabLimit



def fiberPairInverse {d : ℕ} (k : ℕ) (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(z.2:Vector d)-(z.1:Vector d)‖⁻¹ ^ k)

def fiberSlab {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (δ : ℝ)
    (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ∫⁻ C, (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C ∂gaussianRows k d

def fiberPerpendicularTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  ∫⁻ C : Rows k d, (H (fun i => perpendicularRow ((z.2:Vector d)-(z.1:Vector d)) (C i)) : ℝ≥0∞)
    ∂gaussianRows k d

lemma measurable_fiberPairInverse {d k : ℕ} : Measurable (fiberPairInverse (d:=d) k) := by
  unfold fiberPairInverse
  fun_prop

lemma measurable_fiberSlab {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) (δ : ℝ) :
    Measurable (fiberSlab H δ) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hK := measurable_cubeKernel δ
  apply Measurable.lintegral_prod_right
  unfold rowKernel
  fun_prop

lemma measurable_fiberPerpendicularTest {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0) :
    Measurable (fiberPerpendicularTest H) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  apply Measurable.lintegral_prod_right
  apply hH.comp
  unfold perpendicularRow
  fun_prop

lemma normalized_complement_perpendicular {d : ℕ} (v g : Vector d) :
    directionComplement (‖v‖⁻¹ • v) g = perpendicularRow v g := by
  simp only [directionComplement_apply,inner_smul_left,conj_trivial,smul_smul,perpendicularRow]
  congr 2
  rw [div_eq_mul_inv,←inv_pow]
  ring

lemma fiberSlab_limit {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    Tendsto (fun δ : ℝ => fiberSlab H δ z) (𝓝[>] 0)
      (𝓝 (fiberPairInverse k z * (fiberTwoPointConstant k * fiberPerpendicularTest H z))) := by
  have hv : (z.2:Vector d)-(z.1:Vector d) ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hz.symm)
  have ht := gaussian_slab_limit hv H
  simpa only [fiberSlab,fiberPairInverse,fiberTwoPointConstant,fiberPerpendicularTest,
    rowKernel,normalized_complement_perpendicular,gaussianRows] using ht

lemma fiberSlab_le {d k : ℕ} (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) {z : Sphere d×Sphere d} (hz : z.1 ≠ z.2) :
    fiberSlab H δ z ≤ (nndist H 0 : ℝ≥0∞)*fiberPairInverse k z := by
  calc
    _ ≤ ∫⁻ C, (nndist H 0 : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C
        ∂gaussianRows k d := by
      apply lintegral_mono
      intro C
      exact mul_le_mul_left (by
        exact ENNReal.coe_le_coe.mpr (show H C ≤ nndist H 0 by
          simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) C))) _
    _ = (nndist H 0 : ℝ≥0∞)*(∫⁻ C, rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C
        ∂gaussianRows k d) := lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ _ := mul_le_mul_right (gaussian_fresh_kernel_bound (cubeKernel δ) (measurable_cubeKernel δ)
      (lintegral_cubeKernel hδ) k (z.1:Vector d) (z.2:Vector d) (Subtype.coe_injective.ne hz.symm)) _

lemma fiberSlab_integrated_limit {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hne : ∀ᵐ z ∂ρ.prod ρ, z.1 ≠ z.2)
    (hfin : (∫⁻ z, fiberPairInverse k z ∂ρ.prod ρ) ≠ ∞) :
    Tendsto (fun δ : ℝ => ∫⁻ z, fiberSlab H δ z ∂ρ.prod ρ) (𝓝[>] 0)
      (𝓝 (∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z) ∂ρ.prod ρ)) := by
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun z => (nndist H 0 : ℝ≥0∞)*fiberPairInverse k z)
  · exact Eventually.of_forall (measurable_fiberSlab H)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hne.mono (fun z hz => fiberSlab_le H hδ hz)
  · rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  · exact hne.mono (fun z hz => fiberSlab_limit H hz)

lemma cubeAverage_sphereKernel {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    {δ : ℝ} (hδ : 0 < δ) (s : Sphere d) :
    cubeAverage ρ C (label C (s:Vector d)) δ =
      ∫⁻ t : Sphere d, rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂ρ := by
  rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,
    lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C) continuous_subtype_val.measurable]

lemma fiberSlab_tonelli {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) δ
      ∂(gaussianRows k d).prod ρ) = ∫⁻ z, fiberSlab H δ z ∂ρ.prod ρ := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hK := measurable_cubeKernel δ
  have hm : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) δ) :=
    (hH.comp measurable_fst).mul (measurable_own_cube ρ δ)
  have hm' : Measurable (fun z : Rows k d×(Sphere d×Sphere d) =>
      (H z.1 : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.2.1:Vector d) (z.2.2:Vector d) z.1) := by
    unfold rowKernel
    fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [cubeAverage_sphereKernel ρ _ hδ]
  have he (C : Rows k d) :
      (∫⁻ s : Sphere d, (H C : ℝ≥0∞)*(∫⁻ t : Sphere d,
        rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂ρ) ∂ρ) =
      ∫⁻ z : Sphere d×Sphere d, (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C ∂ρ.prod ρ := by
    have hC : Measurable (fun z : Sphere d×Sphere d =>
        (H C : ℝ≥0∞)*rowKernel (cubeKernel δ) (z.1:Vector d) (z.2:Vector d) C) :=
      hm'.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hC.aemeasurable]
    apply lintegral_congr
    intro s
    exact (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
  simp_rw [he]
  exact lintegral_lintegral_swap hm'.aemeasurable

lemma spherical_energy_identity {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw ρ C ≪ volume)
    (hne : ∀ᵐ z ∂ρ.prod ρ, z.1 ≠ z.2)
    (hfin : (∫⁻ z, fiberPairInverse k z ∂ρ.prod ρ) ≠ ∞) :
    (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows k d).prod ρ) =
      ∫⁻ z, fiberPairInverse k z*(fiberTwoPointConstant k*fiberPerpendicularTest H z) ∂ρ.prod ρ := by
  have ht := (fiberSlab_integrated_limit ρ H hne hfin).comp tendsto_cube_scale
  apply tendsto_nhds_unique (spherical_quadratic_limit ρ H hAC)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact (fiberSlab_tonelli ρ H (by positivity)).symm




lemma finite_bounded_withDensity {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (b : A→ℝ≥0∞) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ x, b x ≤ M) :
    IsFiniteMeasure (μ.withDensity b) := by
  apply isFiniteMeasure_withDensity
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (measure_ne_top μ Set.univ))
  calc
    _ ≤ ∫⁻ x, M ∂μ := lintegral_mono hbM
    _ = _ := lintegral_const M

lemma weightedSphere_pair_ne {d : ℕ} (hd : 2 ≤ d) (b : Sphere d→ℝ≥0∞) :
    ∀ᵐ z ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b), z.1 ≠ z.2 := by
  have ha : ∀ᵐ z ∂(uniformSphere d).prod (uniformSphere d), z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {z : Sphere d×Sphere d | z.1 ≠ z.2} from (isClosed_eq continuous_fst continuous_snd).measurableSet.compl)).mpr
    exact ae_of_all _ (fun s => (uniformSphere_ae_ne hd s).mono (fun t ht => ht.symm))
  exact ((withDensity_absolutelyContinuous _ b).prod (withDensity_absolutelyContinuous _ b)).ae_le ha

lemma spherical_pair_inverse_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1) :
    (∫⁻ z, fiberPairInverse k z ∂(uniformSphere d).prod (uniformSphere d)) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (fiberEnergyBound_ne_top d) (measure_ne_top (uniformSphere d) Set.univ))
  calc
    _ = ∫⁻ s : Sphere d, ∫⁻ t : Sphere d, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹ ^ k)
        ∂uniformSphere d ∂uniformSphere d := lintegral_prod _ measurable_fiberPairInverse.aemeasurable
    _ ≤ ∫⁻ s : Sphere d, fiberEnergyBound d ∂uniformSphere d :=
      lintegral_mono (spherical_inverse_bound hk hkd)
    _ = _ := lintegral_const _

lemma weightedSphere_pair_inverse_finite {d k : ℕ} (hk : 1≤k) (hkd : k<d-1)
    (b : Sphere d→ℝ≥0∞) (hb : Measurable b) (M : ℝ≥0∞) (hM : M ≠ ∞) (hbM : ∀ s, b s ≤ M) :
    (∫⁻ z, fiberPairInverse k z ∂((uniformSphere d).withDensity b).prod ((uniformSphere d).withDensity b)) ≠ ∞ := by
  rw [prod_withDensity hb hb,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun z : Sphere d×Sphere d => b z.1*b z.2) from
        (hb.comp measurable_fst).mul (hb.comp measurable_snd)) measurable_fiberPairInverse]
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hM hM) (spherical_pair_inverse_finite hk hkd))
  calc
    _ ≤ ∫⁻ z : Sphere d×Sphere d, (M*M)*fiberPairInverse k z ∂(uniformSphere d).prod (uniformSphere d) := by
      apply lintegral_mono
      intro z
      exact mul_le_mul_left (mul_le_mul (hbM z.1) (hbM z.2) bot_le bot_le) _
    _ = _ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top hM hM)

lemma weightedSphere_projection_ac {d k : ℕ} (hk : 1≤k) (hkd : k<d-1)
    (b : Sphere d→ℝ≥0∞) :
    ∀ᵐ C ∂gaussianRows k d, labelLaw ((uniformSphere d).withDensity b) C ≪ volume := by
  filter_upwards [spherical_projection_ac hk hkd] with C hC
  exact (Measure.AbsolutelyContinuous.map (withDensity_absolutelyContinuous _ b)
      (by unfold label; fun_prop)).trans hC



end CurrentProjection

end

end OAI
