import OAI.Probability.PosteriorReplicas.Regression.SphereBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def ambientSphereLaw : Measure E := (sphereLaw (E := E)).map Subtype.val

instance ambientSphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (ambientSphereLaw (E := E)) := by
  unfold ambientSphereLaw
  infer_instance

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by
  by_cases hr1 : r ≤ 1
  · rw [ambientSphereLaw, Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
    apply (sphereLaw_cap_raw z hr hr1 (Module.finrank_pos (R := ℝ) (M := E))).trans
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)
  · have hr1 : 1 ≤ r := (le_of_not_ge hr1)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply one_le_mul
        · rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : (1 : ℝ) ≤ 4 ^ Module.finrank ℝ E := one_le_pow₀ (by norm_num)
          linarith
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr1)

lemma terminal_cap_mass [Nontrivial E] (y z : E) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (a : ℕ) (ha : 2*a ≤ Module.finrank ℝ E - 1) :
    ((ambientSphereLaw (E := E)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (ε^a) * ENNReal.ofReal (r^a) := by
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le h a) (by positivity)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (2*a) ha).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hε.le a)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm 2 a, pow_mul, pow_two]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

lemma sphere_inner_sq_integrable [Nontrivial E] (v : E) :
    Integrable (fun x => ⟪v,x⟫^2) (ambientSphereLaw (E := E)) := by
  apply (integrable_const (‖v‖^2)).mono' (by fun_prop)
  filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
  have h := abs_real_inner_le_norm v x
  rw [hx, mul_one] at h
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 h)

lemma sphere_inner_sq_eq [Nontrivial E] {v w : E} (h : ‖v‖ = ‖w‖) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = ∫ x, ⟪w,x⟫^2 ∂ambientSphereLaw := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  have hi := (ambientSphereLaw_isometry e).integral_comp
    e.toMeasurableEquiv.measurableEmbedding (fun x => ⟪w,x⟫^2)
  rw [← he] at hi
  simp only [e.inner_map_map] at hi
  simpa only [he] using hi

lemma sphere_inner_sq_unit [Nontrivial E] {v : E} (hv : ‖v‖ = 1) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, (∑ i, ⟪b i,x⟫^2) = ‖x‖^2 := by
    intro x
    simpa only [real_inner_comm x, pow_two, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have h : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw := by
        have heq : ∀ i, (∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw) =
            ∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw := fun i =>
          sphere_inner_sq_eq (by rw [b.norm_eq_one, hv])
        simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i,x⟫^2 ∂ambientSphereLaw :=
        (integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i))).symm
      _ = ∫ _ : E, (1 : ℝ) ∂ambientSphereLaw := by
        apply integral_congr_ae
        filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
        rw [hsum, hx, one_pow]
      _ = 1 := by simp
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact (eq_div_iff hd).2 (by simpa only [mul_comm] using h)

lemma sphere_projection_sq_integrable [Nontrivial E] (U : Submodule ℝ E) :
    Integrable (fun x => ‖U.orthogonalProjectionOnto x‖^2) (ambientSphereLaw (E := E)) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  exact integrable_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))

lemma sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  rw [integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))]
  have hi : ∀ i, (∫ x, ⟪(b i : E), x⟫^2 ∂ambientSphereLaw) =
      1 / (Module.finrank ℝ E : ℝ) := fun i =>
    sphere_inner_sq_unit (by exact b.norm_eq_one i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

def sphereIsometry (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖e x‖ = 1
    rw [e.norm_map])

lemma sphereIsometry_preserving [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry e) (sphereLaw (E := E)) (sphereLaw (E := E)) := by
  refine ⟨(sphereIsometry e).continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (sphereLaw (E := E)).map (e ∘ Subtype.val) = ambientSphereLaw
  rw [← Measure.map_map e.continuous.measurable (by fun_prop)]
  exact (ambientSphereLaw_isometry e).map_eq

omit [MeasurableSpace E] [BorelSpace E] in
lemma reflection_dist (U : Submodule ℝ E) (x : E) :
    dist x (U.reflection x) = 2 * ‖Uᗮ.starProjection x‖ := by
  rw [dist_eq_norm, Submodule.reflection_apply]
  have heq : x - (2 • U.starProjection x - x) = (2 : ℝ) • Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, two_smul ℝ]
    abel
  rw [heq, norm_smul]
  norm_num

lemma sphere_projection_large [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/16 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have : (4 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/4 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/16 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

lemma sphere_reflection_success_bound [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E)
    (S : Set (Metric.sphere (0 : E) 1)) (hS : NullMeasurableSet S sphereLaw)
    (hsep : ∀ s ∈ S, sphereIsometry U.reflection s ∈ S →
      dist s.val (U.reflection s.val) ≤ 1/5) :
    sphereLaw S ≤ ENNReal.ofReal (21/32 : ℝ) := by
  let f := sphereIsometry U.reflection
  have hp := sphereIsometry_preserving U.reflection
  have hi : S ∩ f ⁻¹' S ⊆
      {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} := by
    intro s hs
    have hd := hsep s hs.1 hs.2
    rw [reflection_dist] at hd
    have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
    rw [mem_sphere_zero_iff_norm.mp s.property] at hn
    change (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
    have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
    rw [he] at hn
    nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
  have hinter := (measure_mono hi).trans (sphere_projection_large U hU)
  have heq := measure_union_add_inter₀ S (hS.preimage hp.quasiMeasurePreserving)
  rw [hp.measure_preimage hS] at heq
  calc
    sphereLaw S = ENNReal.ofReal (1/2 : ℝ) * (sphereLaw S + sphereLaw S) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2 : ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ = ENNReal.ofReal (1/2 : ℝ) *
        (sphereLaw (S ∪ f ⁻¹' S) + sphereLaw (S ∩ f ⁻¹' S)) := by rw [heq]
    _ ≤ ENNReal.ofReal (1/2 : ℝ) * (1 + ENNReal.ofReal (5/16 : ℝ)) := by
      exact mul_le_mul' le_rfl (add_le_add prob_le_one hinter)
    _ = ENNReal.ofReal (21/32 : ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num

end MoreSphere

end PosteriorRegression
end

end OAI
