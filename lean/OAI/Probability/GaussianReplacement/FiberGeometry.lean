import OAI.Probability.GaussianReplacement.FiberModel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



section GaussianDirection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def directionComplement (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ u).smulRight u

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma directionComplement_apply (u g : E) : directionComplement u g = g - ⟪u,g⟫ • u := rfl

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma directionComplement_inner (u g y : E) :
    ⟪y,directionComplement u g⟫ = ⟪y-⟪u,y⟫ • u,g⟫ := by
  simp only [directionComplement_apply,inner_sub_right,inner_smul_right,inner_sub_left,
    inner_smul_left,conj_trivial,real_inner_comm u y]
  ring

lemma gaussian_direction_indep {u : E} (hu : ‖u‖ = 1) :
    IndepFun (fun g : E => ⟪u,g⟫) (directionComplement u) (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun
    ((innerSL ℝ u).prod (directionComplement u))
  change HasGaussianLaw (fun g : E => (⟪u,g⟫,directionComplement u g)) (stdGaussian E) at hG
  apply hG.indepFun_of_covariance_inner
  intro x y
  have he : (fun g : E => ⟪x,⟪u,g⟫⟫) = fun g => ⟪x • u,g⟫ := by
    funext g
    simp only [Real.inner_apply,inner_smul_left,conj_trivial]
  simp_rw [he,directionComplement_inner]
  rw [←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  change ⟪x • u,y-⟪u,y⟫ • u⟫ = 0
  simp only [inner_smul_left,conj_trivial,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
  ring

lemma gaussian_direction_real {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => ⟪u,g⟫) = gaussianReal 0 1 := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian E)).map_fun (innerSL ℝ u)
  change HasGaussianLaw (fun g : E => ⟪u,g⟫) (stdGaussian E) at hG
  rw [hG.map_eq_gaussianReal]
  have hi : (∫ g : E, ⟪u,g⟫ ∂stdGaussian E) = 0 := integral_strongDual_stdGaussian (innerSL ℝ u)
  have hv : Var[fun g : E => ⟪u,g⟫; stdGaussian E] = 1 := by
    rw [←covariance_self (by fun_prop),←covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,innerSL_apply_apply,real_inner_self_eq_norm_sq,hu,one_pow]
  simp only [hi,hv,Real.toNNReal_one]

lemma gaussian_direction_split {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g => (⟪u,g⟫,directionComplement u g)) =
      (gaussianReal 0 1).prod ((stdGaussian E).map (directionComplement u)) := by
  rw [(gaussian_direction_indep hu).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    gaussian_direction_real hu]

end GaussianDirection

section GaussianDirectionRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_direction_rows_split {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map
      (fun G => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) =
      (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin k => (stdGaussian E).map (directionComplement u))) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ E (Fin k)
  have he : (fun G : Fin k→E => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) =
      e ∘ (fun G => fun i => (⟪u,G i⟫,directionComplement u (G i))) := rfl
  rw [he,←Measure.map_map e.measurable (by fun_prop),
    Measure.pi_map_pi (f := fun (_ : Fin k) => fun g : E => (⟪u,g⟫,directionComplement u g))
      (μ := fun _ => stdGaussian E) (fun i => by fun_prop)]
  simp_rw [gaussian_direction_split hu]
  exact (measurePreserving_arrowProdEquivProdArrow ℝ E (Fin k)
    (fun _ => gaussianReal 0 1) (fun _ => (stdGaussian E).map (directionComplement u))).map_eq

lemma gaussian_direction_rows_recover {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin k => (stdGaussian E).map (directionComplement u)))).map
      (fun z => fun i => z.1 i • u+z.2 i) = Measure.pi (fun _ : Fin k => stdGaussian E) := by
  rw [←gaussian_direction_rows_split hu k,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z : (Fin k→ℝ)×(Fin k→E) => fun i => z.1 i • u+z.2 i) ∘
      (fun G : Fin k→E => ((fun i => ⟪u,G i⟫),(fun i => directionComplement u (G i)))) = id := by
    funext G i
    simp [directionComplement_apply]
  rw [he,Measure.map_id]
end GaussianDirectionRows




section FiberAverage
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X)

lemma tendsto_normalized_closedBall {f : X → ℝ≥0∞} {x : X}
    (hf : ContinuousAt f x)
    (hvol : ∀ r : ℝ, 0 < r → μ (Metric.closedBall x r) ≠ 0 ∧
      μ (Metric.closedBall x r) ≠ ∞) :
    Tendsto (fun r : ℝ => (μ (Metric.closedBall x r))⁻¹ *
      ∫⁻ y in Metric.closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨b,hab,hb⟩ := exists_between ha
    have hnb : {y | b < f y} ∈ 𝓝 x := hf (Ioi_mem_nhds hb)
    have he : ∀ᶠ r in 𝓝[>] (0:ℝ), Metric.closedBall x r ⊆ _ :=
      (eventually_closedBall_subset hnb).filter_mono inf_le_left
    filter_upwards [he, self_mem_nhdsWithin] with r hr hr0
    have hv := hvol r hr0
    apply hab.trans_le
    calc
      b = (μ (Metric.closedBall x r))⁻¹ * (b * μ (Metric.closedBall x r)) := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hv.1 hv.2, mul_one]
      _ ≤ _ := mul_le_mul_right (by
        rw [←setLIntegral_const]
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro y hy
        exact (hr hy).le) _
  · intro a ha
    obtain ⟨b,hb,hba⟩ := exists_between ha
    have hnb : {y | f y < b} ∈ 𝓝 x := hf (Iio_mem_nhds hb)
    have he : ∀ᶠ r in 𝓝[>] (0:ℝ), Metric.closedBall x r ⊆ _ :=
      (eventually_closedBall_subset hnb).filter_mono inf_le_left
    filter_upwards [he, self_mem_nhdsWithin] with r hr hr0
    have hv := hvol r hr0
    apply lt_of_le_of_lt _ hba
    calc
      _ ≤ (μ (Metric.closedBall x r))⁻¹ * (b * μ (Metric.closedBall x r)) := by
        apply mul_le_mul_right
        rw [←setLIntegral_const]
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro y hy
        exact (hr hy).le
      _ = b := by rw [mul_left_comm, ENNReal.inv_mul_cancel hv.1 hv.2,mul_one]
end FiberAverage

lemma ennreal_double_mul_le_sq_add (a b : ℝ≥0∞) : 2*(a*b) ≤ a^2+b^2 := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  norm_num only [ENNReal.rpow_two,ENNReal.ofReal_ofNat] at h
  calc
    _ ≤ 2*(a^2/2+b^2/2) := mul_le_mul_right h 2
    _ = _ := by
      rw [mul_add,div_eq_mul_inv,div_eq_mul_inv]
      rw [mul_left_comm 2, mul_left_comm 2]
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      simp

lemma cube_energy_contraction {k : ℕ} (p K : (Fin k → ℝ) → ℝ≥0∞)
    (hp : Measurable p) (hK : Measurable K) (hKn : ∫⁻ z, K z = 1) :
    (∫⁻ x, ∫⁻ y, p x*p y*K (y-x)) ≤ ∫⁻ x, p x^2 := by
  have hA : (∫⁻ x, ∫⁻ y, p x^2*K (y-x)) = ∫⁻ x, p x^2 := by
    congr 1
    funext x
    rw [lintegral_const_mul _ (show Measurable (fun y => K (y-x)) by fun_prop),
      lintegral_sub_right_eq_self,hKn,mul_one]
  have hB : (∫⁻ x, ∫⁻ y, p y^2*K (y-x)) = ∫⁻ y, p y^2 := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    congr 1
    funext y
    rw [lintegral_const_mul _ (show Measurable (fun x => K (y-x)) by fun_prop),
      lintegral_sub_left_eq_self,hKn,mul_one]
  have he : 2*(∫⁻ x, ∫⁻ y, p x*p y*K (y-x)) ≤ 2*(∫⁻ x, p x^2) := by
    calc
      _ = ∫⁻ x, ∫⁻ y, 2*(p x*p y)*K (y-x) := by
        simp_rw [mul_assoc,lintegral_const_mul' (2:ℝ≥0∞) _ (by norm_num)]
      _ ≤ ∫⁻ x, ∫⁻ y, (p x^2+p y^2)*K (y-x) := by
        apply lintegral_mono
        intro x
        apply lintegral_mono
        intro y
        exact mul_le_mul_left (ennreal_double_mul_le_sq_add _ _) _
      _ = (∫⁻ x, ∫⁻ y, p x^2*K (y-x)) + (∫⁻ x, ∫⁻ y, p y^2*K (y-x)) := by
        simp_rw [add_mul]
        rw [show (fun x => ∫⁻ y, p x^2*K (y-x)+p y^2*K (y-x)) =
          (fun x => (∫⁻ y, p x^2*K (y-x))+(∫⁻ y, p y^2*K (y-x))) by
            funext x; exact lintegral_add_left (by fun_prop) _]
        exact lintegral_add_left (by fun_prop) _
      _ = _ := by rw [hA,hB,two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mp he



lemma continuous_lintegral_bounded {A X : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : A → X → ℝ≥0∞) (hf : ∀ x, Continuous (fun a => f a x))
    (hm : ∀ a, Measurable (f a)) (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hb : ∀ a x, f a x ≤ M) : Continuous (fun a => ∫⁻ x, f a x ∂μ) := by
  apply continuous_iff_continuousAt.2
  intro a
  exact tendsto_lintegral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall hm) (Eventually.of_forall (fun a => ae_of_all _ (hb a)))
    (by simp only [lintegral_const]; exact ENNReal.mul_ne_top hM (measure_ne_top _ _))
    (ae_of_all _ (fun x => (hf x).continuousAt))

lemma tendsto_scaled_cube_average {k : ℕ} (F : (Fin k→ℝ) → ℝ≥0∞)
    (hF : ContinuousAt F 0) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal ((2*δ)⁻¹ ^ k) *
      ∫⁻ z in Metric.closedBall (0 : Fin k→ℝ) (δ/r), F z)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (r⁻¹ ^ k) * F 0)) := by
  have hv : ∀ a : ℝ, 0 < a →
      (volume : Measure (Fin k→ℝ)) (Metric.closedBall 0 a) ≠ 0 ∧
      (volume : Measure (Fin k→ℝ)) (Metric.closedBall 0 a) ≠ ∞ := by
    intro a ha
    rw [Real.volume_pi_closedBall 0 ha.le]
    constructor
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · exact ENNReal.ofReal_ne_top
  have hz : Tendsto (fun δ : ℝ => δ/r) (𝓝[>] (0:ℝ)) (𝓝 (0/r)) :=
    ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0:ℝ)) (𝓝 (0:ℝ))).mono_left
      (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)).div_const r
  rw [zero_div] at hz
  have ht := (tendsto_normalized_closedBall volume hF hv).comp
    (show Tendsto (fun δ : ℝ => δ/r) (𝓝[>] 0) (𝓝[>] 0) from
      tendsto_nhdsWithin_iff.2 ⟨hz,
        by filter_upwards [self_mem_nhdsWithin] with δ hδ; exact div_pos hδ hr⟩)
  have ht' := ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (r⁻¹ ^ k) ≠ ∞))
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  dsimp only [Function.comp_def]
  rw [Real.volume_pi_closedBall 0 (div_nonneg hδ.le hr.le)]
  simp only [Fintype.card_fin]
  rw [←mul_assoc]
  congr 1
  rw [←ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < (2*(δ/r))^k),
    ←ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [inv_pow]
  rw [←mul_inv_rev,←mul_pow]
  congr 2
  field_simp

section GaussianSlab
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def gaussianReconstruct (u : E) {k : ℕ} (zG : (Fin k→ℝ)×(Fin k→E)) : Fin k→E :=
  fun i => zG.1 i • u + directionComplement u (zG.2 i)

lemma gaussian_reconstruct_law {u : E} (hu : ‖u‖ = 1) (k : ℕ) :
    ((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
      (Measure.pi (fun _ : Fin k => stdGaussian E))).map (gaussianReconstruct u) =
      Measure.pi (fun _ : Fin k => stdGaussian E) := by
  have hm : Measurable (fun G : Fin k→E => fun i => directionComplement u (G i)) := by fun_prop
  have he := Measure.pi_map_pi (μ := fun _ : Fin k => stdGaussian E)
    (f := fun _ => directionComplement u) (fun _ => (directionComplement u).measurable.aemeasurable)
  calc
    _ = (((Measure.pi (fun _ : Fin k => gaussianReal 0 1)).prod
      ((Measure.pi (fun _ : Fin k => stdGaussian E)).map
        (fun G => fun i => directionComplement u (G i)))).map
        (fun z => fun i => z.1 i • u+z.2 i)) := by
      rw [show Measure.pi (fun _ : Fin k => gaussianReal 0 1) =
        (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map id by rw [Measure.map_id],
        Measure.map_prod_map _ _ measurable_id hm,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rw [Measure.map_id]
      rfl
    _ = _ := by rw [he]; exact gaussian_direction_rows_recover hu k

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma gaussian_reconstruct_pairing {u : E} (hu : ‖u‖ = 1) {k : ℕ}
    (zG : (Fin k→ℝ)×(Fin k→E)) (i : Fin k) :
    ⟪u,gaussianReconstruct u zG i⟫ = zG.1 i := by
  simp [gaussianReconstruct,directionComplement_apply,inner_add_right,
    inner_sub_right,inner_smul_right,hu]

lemma continuous_gaussian_slice {u : E} {k : ℕ} (H : BoundedContinuousFunction (Fin k→E) ℝ≥0) :
    Continuous (fun z : Fin k→ℝ => ∫⁻ G : Fin k→E,
      (H (gaussianReconstruct u (z,G)) : ℝ≥0∞) ∂Measure.pi (fun _ => stdGaussian E)) := by
  apply continuous_lintegral_bounded _ (fun G => by
    apply ENNReal.continuous_coe.comp
    exact H.continuous.comp (by unfold gaussianReconstruct; fun_prop))
    (fun z => by apply ENNReal.continuous_coe.measurable.comp
                 exact H.continuous.measurable.comp (by unfold gaussianReconstruct; fun_prop))
    ((nndist H 0 : ℝ≥0) : ℝ≥0∞) ENNReal.coe_ne_top
  intro z G
  apply ENNReal.coe_le_coe.mpr
  simpa using (BoundedContinuousFunction.nndist_coe_le_nndist (f:=H) (g:=0) (gaussianReconstruct u (z,G)))
end GaussianSlab




def fiberEnergyBound (d : ℕ) : ℝ≥0∞ := momentConstant 9 d (3*4^d) (3*4^d)

lemma fiberEnergyBound_ne_top (d : ℕ) : fiberEnergyBound d ≠ ∞ := ENNReal.ofReal_ne_top

lemma uniformSphere_ae_ne {d : ℕ} (hd : 2 ≤ d) (s : Sphere d) :
    ∀ᵐ t ∂uniformSphere d, t ≠ s := by
  have hz := (uniformSphere_growth (by omega : 1 ≤ d) (le_refl (d-1))).sphereLift.affine_span_null
    (by positivity) (⊥ : Submodule ℝ (Vector d)) (s:Vector d) (by simp; omega)
    (sphereLift_ae_norm_sub_le (uniformSphere d) s)
  simp only [Submodule.mem_bot,sub_eq_zero] at hz
  rw [sphereLift,Measure.map_apply continuous_subtype_val.measurable (show MeasurableSet {u : Vector d | u = (s:Vector d)} from isClosed_eq continuous_id continuous_const |>.measurableSet)] at hz
  simpa only [ae_iff,not_not,Set.preimage_ofPred_eq,Subtype.val_inj] using hz

lemma spherical_inverse_bound {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1)
    (s : Sphere d) :
    (∫⁻ t : Sphere d, ENNReal.ofReal (‖(t:Vector d)-(s:Vector d)‖⁻¹ ^ k)
      ∂uniformSphere d) ≤ fiberEnergyBound d := by
  have hB : AmbientGrowth (sphereLift (uniformSphere d)) (0+k) (3*4^d) := by
    simpa only [zero_add] using (uniformSphere_growth (by omega : 1 ≤ d) hkd.le).sphereLift
  have hh := hB.mixed_inverse_uniform
    ((uniformSphere_growth (by omega : 1 ≤ d) (le_refl (d-1))).sphereLift)
    (by positivity) (by positivity) (m:=0) (by simpa using hkd) (Nat.sub_le d 1)
    (⊥ : Submodule ℝ (Vector d)) (s:Vector d) (by simpa using hk)
    (sphereLift_ae_norm_sub_le (uniformSphere d) s)
  rw [sphereLift,lintegral_map (measurable_mixedInverse _ _ _ _) continuous_subtype_val.measurable] at hh
  simpa only [mixedInverse,pow_zero,mul_one,fiberEnergyBound] using hh

lemma spherical_cube_expectation {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1)
    (s : Sphere d) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ C, cubeAverage (uniformSphere d) C (label C (s:Vector d)) δ
      ∂gaussianRows k d) ≤ fiberEnergyBound d := by
  have he : ∀ C : Rows k d, cubeAverage (uniformSphere d) C (label C (s:Vector d)) δ =
      ∫⁻ t : Sphere d, rowKernel (cubeKernel δ) (s:Vector d) (t:Vector d) C ∂uniformSphere d := by
    intro C
    rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,
      lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C)
        continuous_subtype_val.measurable]
  simp_rw [he]
  have hK := measurable_cubeKernel δ
  rw [lintegral_lintegral_swap (by dsimp [rowKernel]; fun_prop)]
  apply le_trans _ (spherical_inverse_bound hk hkd s)
  apply lintegral_mono_ae
  filter_upwards [uniformSphere_ae_ne (by omega) s] with t ht
  exact gaussian_fresh_kernel_bound (cubeKernel δ) (measurable_cubeKernel δ)
    (lintegral_cubeKernel hδ) k (s:Vector d) (t:Vector d) (Subtype.coe_injective.ne ht)

lemma spherical_extended_energy {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1) :
    (∫⁻ z : Rows k d×Sphere d,
      extendedCubeDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows k d).prod (uniformSphere d)) ≤ fiberEnergyBound d := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  change (∫⁻ z, liminf (fun j : ℕ => cubeAverage (uniformSphere d) z.1
    (label z.1 (z.2:Vector d)) (1/(j:ℝ))) atTop
    ∂(gaussianRows k d).prod (uniformSphere d)) ≤ _
  apply (lintegral_liminf_le (fun j => measurable_own_cube (uniformSphere d) _)).trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with j hj
  rw [lintegral_prod _ (measurable_own_cube (k:=k) (uniformSphere d) _).aemeasurable,
    lintegral_lintegral_swap (measurable_own_cube (k:=k) (uniformSphere d) _).aemeasurable]
  calc
    _ ≤ ∫⁻ s : Sphere d, fiberEnergyBound d ∂uniformSphere d := by
      apply lintegral_mono
      intro s
      exact spherical_cube_expectation hk hkd s (by positivity)
    _ = _ := by simp

lemma spherical_projection_ac {d k : ℕ} (hk : 1 ≤ k) (hkd : k < d-1) :
    ∀ᵐ C ∂gaussianRows k d, labelLaw (uniformSphere d) C ≪ volume := by
  have hf := ae_lt_top (measurable_own_extended (k:=k) (uniformSphere d))
    (ne_of_lt (lt_of_le_of_lt (spherical_extended_energy hk hkd) (lt_top_iff_ne_top.mpr (fiberEnergyBound_ne_top d))))
  have hff := Measure.ae_ae_of_ae_prod hf
  filter_upwards [hff] with C hC
  exact labelLaw_ac_of_finite_extended (uniformSphere d) C hC




lemma projection_convolution_contraction {k : ℕ} (μ : Measure (Fin k→ℝ))
    (p K : (Fin k→ℝ) → ℝ≥0∞) (hp : Measurable p) (hK : Measurable K)
    (hμ : volume.withDensity p = μ) (hKn : ∫⁻ z, K z = 1) :
    (∫⁻ x, ∫⁻ y, K (y-x) ∂μ ∂μ) ≤ ∫⁻ x, p x ∂μ := by
  rw [←hμ]
  have hi (x : Fin k→ℝ) : (∫⁻ y, K (y-x) ∂volume.withDensity p) =
      ∫⁻ y, p y*K (y-x) := by
    exact lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)
  simp_rw [hi]
  rw [lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp hp]
  simp only [Pi.mul_apply]
  have he : (∫⁻ x, p x*(∫⁻ y, p y*K (y-x))) =
      ∫⁻ x, ∫⁻ y, p x*p y*K (y-x) := by
    congr 1
    funext x
    rw [←lintegral_const_mul _ (show Measurable (fun y => p y*K (y-x)) by fun_prop)]
    simp only [mul_assoc]
  rw [he]
  simpa only [pow_two] using cube_energy_contraction p K hp hK hKn

lemma cubeVectorKernel_normalized {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ z : Fin k→ℝ, ∏ i, cubeKernel δ (z i)) = 1 := by
  rw [volume_pi,lintegral_fin_prod (volume : Measure ℝ) k (fun _ => cubeKernel δ) (fun _ => (measurable_cubeKernel δ))]
  simp [lintegral_cubeKernel hδ]

lemma cubeAverage_labelKernel {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    {δ : ℝ} (hδ : 0 < δ) (s : Sphere d) :
    cubeAverage ρ C (label C (s:Vector d)) δ =
      ∫⁻ y, ∏ i, cubeKernel δ (y i-label C (s:Vector d) i) ∂labelLaw ρ C := by
  rw [cubeAverage_eq_kernel _ _ hδ.le,sphereLift,labelLaw,
    lintegral_map (measurable_rowKernel_left _ (measurable_cubeKernel δ) _ _ C) continuous_subtype_val.measurable,
    lintegral_map (by have := measurable_cubeKernel δ; fun_prop) (by unfold label; fun_prop)]
  congr 1
  funext t
  simp only [rowKernel,label,inner_sub_left]

lemma spherical_cube_energy_eq {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (C : Rows k d) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ s : Sphere d, cubeAverage ρ C (label C (s:Vector d)) δ ∂ρ) =
      ∫⁻ x, ∫⁻ y, (∏ i, cubeKernel δ ((y-x) i)) ∂labelLaw ρ C ∂labelLaw ρ C := by
  have hK : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (z i)) := by
    have := measurable_cubeKernel δ
    fun_prop
  have hf : Measurable (fun s : Sphere d => label C (s:Vector d)) := by unfold label; fun_prop
  have hm : Measurable (fun x : Fin k→ℝ => ∫⁻ y,
      (∏ i, cubeKernel δ ((y-x) i)) ∂labelLaw ρ C) :=
    Measurable.lintegral_prod_right (hK.comp (measurable_snd.sub measurable_fst))
  calc
    _ = ∫⁻ s : Sphere d, ∫⁻ y, (∏ i, cubeKernel δ ((y-label C (s:Vector d)) i)) ∂labelLaw ρ C ∂ρ := by
      apply lintegral_congr
      intro s
      exact cubeAverage_labelKernel ρ C hδ s
    _ = _ := (lintegral_map hm hf).symm

lemma lintegral_labelLaw {d k : ℕ} (ρ : Measure (Sphere d)) (C : Rows k d)
    (f : (Fin k→ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂labelLaw ρ C) = ∫⁻ s : Sphere d, f (label C (s:Vector d)) ∂ρ :=
  lintegral_map hf (by unfold label; fun_prop)

lemma spherical_cube_energy_le {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (C : Rows k d) (hC : labelLaw ρ C ≪ volume) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ s : Sphere d, cubeAverage ρ C (label C (s:Vector d)) δ ∂ρ) ≤
      ∫⁻ s : Sphere d, exactDensity ρ C (label C (s:Vector d)) ∂ρ := by
  have hpair : Measurable (fun y : Fin k→ℝ => (C,y)) := measurable_const.prodMk measurable_id
  have hp := (measurable_exactDensity (k:=k) ρ).comp hpair
  change Measurable (fun y : Fin k→ℝ => exactDensity ρ C y) at hp
  have hK : Measurable (fun z : Fin k→ℝ => ∏ i, cubeKernel δ (z i)) := by
    have := measurable_cubeKernel δ
    fun_prop
  rw [spherical_cube_energy_eq ρ C hδ]
  calc
    _ ≤ ∫⁻ y, exactDensity ρ C y ∂labelLaw ρ C :=
      projection_convolution_contraction (labelLaw ρ C) (fun y => exactDensity ρ C y)
        (fun z => ∏ i, cubeKernel δ (z i)) hp hK
        (labelLaw_withDensity_exact ρ C hC) (cubeVectorKernel_normalized (k:=k) hδ)
    _ = _ := lintegral_labelLaw ρ C _ hp

lemma spherical_quadratic_limit {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (H : BoundedContinuousFunction (Rows k d) ℝ≥0)
    (hAC : ∀ᵐ C ∂gaussianRows k d, labelLaw ρ C ≪ volume) :
    Tendsto (fun j : ℕ => ∫⁻ z : Rows k d×Sphere d,
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))
      ∂(gaussianRows k d).prod ρ) atTop
      (𝓝 (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
        ∂(gaussianRows k d).prod ρ)) := by
  have hH : Measurable (fun C => (H C : ℝ≥0∞)) := ENNReal.continuous_coe.measurable.comp H.continuous.measurable
  have hm (j : ℕ) : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))) :=
    (hH.comp measurable_fst).mul (measurable_own_cube ρ _)
  have hlim : ∀ᵐ z : Rows k d×Sphere d ∂(gaussianRows k d).prod ρ,
      Tendsto (fun j : ℕ => cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ)))
        atTop (𝓝 (exactDensity ρ z.1 (label z.1 (z.2:Vector d)))) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun
      (fun j : ℕ => measurable_own_cube (k:=k) ρ (1/(j:ℝ))) (measurable_own_exact ρ))).mpr
    filter_upwards [hAC] with C hC
    exact ae_of_ae_map (by unfold label; fun_prop) (hC.ae_le (volume_ae_cube_limit ρ C))
  have hlow : (∫⁻ z : Rows k d×Sphere d, (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))
        ∂(gaussianRows k d).prod ρ) ≤
      liminf (fun j : ℕ => ∫⁻ z : Rows k d×Sphere d,
      (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))
      ∂(gaussianRows k d).prod ρ) atTop := by
    calc
      _ = ∫⁻ z : Rows k d×Sphere d, liminf (fun j : ℕ =>
          (H z.1 : ℝ≥0∞)*cubeAverage ρ z.1 (label z.1 (z.2:Vector d)) (1/(j:ℝ))) atTop
          ∂(gaussianRows k d).prod ρ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with z hz
        exact (ENNReal.Tendsto.const_mul hz (Or.inr ENNReal.coe_ne_top)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le hm
  apply tendsto_of_le_liminf_of_limsup_le hlow
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hmExact : Measurable (fun z : Rows k d×Sphere d =>
      (H z.1 : ℝ≥0∞)*exactDensity ρ z.1 (label z.1 (z.2:Vector d))) :=
    (hH.comp measurable_fst).mul (measurable_own_exact ρ)
  rw [lintegral_prod _ (hm j).aemeasurable,lintegral_prod _ hmExact.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [hAC] with C hC
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  exact mul_le_mul_right (spherical_cube_energy_le ρ C hC (by positivity)) _



end CurrentProjection

end

end OAI
