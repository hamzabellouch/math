import OAI.Probability.GaussianReplacement.HybridModel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



section KernelGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]

def rowSpan {r : ℕ} (A : Fin r → E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range A)

def rowProjectionL {r : ℕ} (A : Fin r → E) : E →L[ℝ] E :=
  ∑ i, (‖gramSchmidt ℝ A i‖ ^ 2)⁻¹ •
    InnerProductSpace.rankOne ℝ (gramSchmidt ℝ A i) (gramSchmidt ℝ A i)

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_eq {r : ℕ} (A : Fin r → E) :
    rowProjectionL A = (rowSpan A).starProjection := by
  ext v
  have hgs := gramSchmidt_eq_sub_starProjection (Fin.snoc A v) (Fin.last r)
  rw [image_Iio_last] at hgs
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hgs
  have he := gramSchmidt_def ℝ (Fin.snoc A v) (Fin.last r)
  rw [Fin.Iio_last_eq_map, Finset.sum_map] at he
  simp only [Fin.castSuccEmb_apply, Fin.snoc_last, gramSchmidt_castSucc,
    Fin.snoc_castSucc, Submodule.starProjection_singleton] at he
  have hz : (rowSpan A).starProjection v =
      ∑ i, (⟪gramSchmidt ℝ A i, v⟫ / ‖gramSchmidt ℝ A i‖ ^ 2) • gramSchmidt ℝ A i := by
    dsimp only [rowSpan]
    have := hgs.symm.trans he
    exact (sub_right_inj).mp this
  rw [hz]
  simp only [rowProjectionL, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv, mul_comm]

lemma measurable_rowProjectionL (r : ℕ) :
    Measurable (rowProjectionL (E:=E) (r:=r)) := by
  apply Finset.measurable_sum
  intro i _
  have hg := measurable_gramSchmidt (E:=E) i
  have hr : Measurable (fun A : Fin r → E =>
      InnerProductSpace.rankOne ℝ (gramSchmidt ℝ A i) (gramSchmidt ℝ A i)) := by
    exact (show Continuous (fun x : E => InnerProductSpace.rankOne ℝ x x) from
      (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp₂ (innerSL ℝ).continuous continuous_id).measurable.comp hg
  exact (hg.norm.pow_const 2 |>.inv).smul hr

omit finiteDimensionalRealE measurableSpaceE borelSpaceE in
lemma rowSpan_isometry {r : ℕ} (A : Fin r → E) (f : E ≃ₗᵢ[ℝ] E) :
    rowSpan (fun i => f (A i)) = (rowSpan A).map f.toLinearEquiv.toLinearMap := by
  rw [rowSpan, rowSpan, Submodule.map_span, ← Set.range_comp]
  rfl

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_isometry {r : ℕ} (A : Fin r → E) (f : E ≃ₗᵢ[ℝ] E) (v : E) :
    rowProjectionL (fun i => f (A i)) (f v) = f (rowProjectionL A v) := by
  rw [rowProjectionL_eq, rowProjectionL_eq, rowSpan_isometry]
  exact (f.toLinearIsometry.map_starProjection' (rowSpan A) v).symm

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_contraction {r : ℕ} (A : Fin r → E) (v : E) :
    ‖rowProjectionL A v‖ ≤ ‖v‖ := by
  rw [rowProjectionL_eq]
  exact (rowSpan A).norm_starProjection_apply_le v

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_perpendicular {r : ℕ} (A : Fin r → E) (v : E) :
    v - rowProjectionL A v ∈ (rowSpan A)ᗮ := by
  rw [rowProjectionL_eq]
  exact (rowSpan A).sub_starProjection_mem_orthogonal v

omit measurableSpaceE borelSpaceE in
lemma rowProjectionL_infDist {r : ℕ} (A : Fin r → E) (v : E) :
    ‖rowProjectionL A v‖ = Metric.infDist v ((rowSpan A)ᗮ : Set E) := by
  rw [rowProjectionL_eq]
  have he : v - (rowSpan A)ᗮ.starProjection v = (rowSpan A).starProjection v := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  rw [← he, Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

lemma gaussianRowIsometry_preserving (r : ℕ) (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (fun A : Fin r → E => fun i => f (A i))
      (Measure.pi fun _ => stdGaussian E) (Measure.pi fun _ => stdGaussian E) :=
  measurePreserving_pi _ _ (fun _ => ⟨f.continuous.measurable, stdGaussian_map f⟩)


lemma rowProjection_smallBall_eq {r : ℕ} (v w : E) (h : ‖v‖ = ‖w‖) (t : ℝ) :
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A v‖ ≤ t} =
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A w‖ ≤ t} := by
  let f := Submodule.reflection (ℝ ∙ (v-w))ᗮ
  have hf : f v = w := Submodule.reflection_sub h
  have hm : MeasurableSet {A : Fin r → E | ‖rowProjectionL A w‖ ≤ t} :=
    measurableSet_le ((measurable_rowProjectionL r).apply_continuousLinearMap w).norm measurable_const
  rw [← (gaussianRowIsometry_preserving r f).measure_preimage hm.nullMeasurableSet]
  congr 1
  ext A
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← hf, rowProjectionL_isometry, f.norm_map]

end KernelGeometry



section GaussianRank
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_submodule_null (V : Submodule ℝ E)
    (hV : Module.finrank ℝ V < Module.finrank ℝ E) : stdGaussian E (V:Set E) = 0 := by
  have hne : Vᗮ ≠ ⊥ := by
    intro h
    have hn := V.finrank_add_finrank_orthogonal
    rw [h, finrank_bot, add_zero] at hn
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let f : StrongDual ℝ E := innerSL ℝ w
  have hf : ‖f‖ ≠ 0 := by simpa [f] using norm_ne_zero_iff.mpr hw0
  have hp : (‖f‖^2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_ne_zero hf))
  have hmap : (stdGaussian E).map f = gaussianReal 0 (‖f‖^2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  have hn : stdGaussian E {x | f x = 0} = 0 := by
    have hs : (gaussianReal 0 (‖f‖^2).toNNReal) {0} = 0 := by
      let := nullSingletonClass_gaussianReal (μ:=0) hp
      exact measure_singleton 0
    rw [← hmap, Measure.map_apply f.measurable (measurableSet_singleton 0)] at hs
    exact hs
  apply le_antisymm _ bot_le
  calc
    stdGaussian E (V:Set E) ≤ stdGaussian E {x | f x = 0} := by
      apply measure_mono
      intro x hx
      change ⟪w,x⟫ = 0
      simpa only [real_inner_comm] using hw x hx
    _ = 0 := hn

lemma gaussianRows_ae_gramSchmidt_ne_zero (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∀ᵐ v : Fin k → E ∂Measure.pi (fun _ => stdGaussian E),
      ∀ i, gramSchmidt ℝ v i ≠ 0 := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ k ih =>
    have hm : MeasurableSet {v : Fin (k+1) → E | ∀ i, gramSchmidt ℝ v i ≠ 0} := by
      simpa only [Set.compl_ofPred, Set.iInter_ofPred] using (MeasurableSet.iInter fun i : Fin (k+1) =>
        (measurableSet_eq_fun (measurable_gramSchmidt (E:=E) i)
          (measurable_const (a:=(0:E)))).compl)
    rw [ae_pi_snoc (stdGaussian E) hm]
    filter_upwards [ih (by omega)] with v hv
    let V := rowSpan v
    have hd : Module.finrank ℝ V ≤ k := by
      change Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ k
      exact (finrank_range_le_card (R:=ℝ) v).trans_eq (Fintype.card_fin k)
    have hn : stdGaussian E (V:Set E) = 0 := stdGaussian_submodule_null V (by omega)
    have ha : ∀ᵐ x ∂stdGaussian E, x ∉ V := by
      rw [ae_iff]
      simp only [not_not]
      change stdGaussian E (V:Set E) = 0
      exact hn
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((V.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨0, V.zero_mem⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

lemma gaussianRows_ae_rowSpan_finrank (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin k → E ∂Measure.pi (fun _ => stdGaussian E),
      Module.finrank ℝ (rowSpan A) = k := by
  filter_upwards [gaussianRows_ae_gramSchmidt_ne_zero k hk] with A hA
  have hi : LinearIndependent ℝ A := by
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [det_gram_eq_prod_gramSchmidt]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hA i))
  change Module.finrank ℝ (Submodule.span ℝ (Set.range A)) = k
  exact (finrank_span_eq_card hi).trans (Fintype.card_fin k)

end GaussianRank



section SphereTubes
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma sphereLaw_submodule_tube (V : Submodule ℝ E) (k : ℕ)
    (hk : Module.finrank ℝ V + k ≤ Module.finrank ℝ E)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    sphereLaw {v : Metric.sphere (0:E) 1 | Metric.infDist (v:E) (V:Set E) ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^k) := by
  let L := V.toAffineSubspace
  let : Nonempty L := ⟨⟨0,V.zero_mem⟩⟩
  have hd : (Module.finrank ℝ L.direction : ℝ) + k ≤ Module.finrank ℝ E := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    exact_mod_cast hk
  have hsub : Set.Ioo (0:ℝ) 1 • (Subtype.val ''
      {v : Metric.sphere (0:E) 1 | Metric.infDist (v:E) (V:Set E) ≤ t}) ⊆
      {v:E | Metric.infDist v L ≤ t} := by
    rintro _ ⟨c,hc,_,⟨v,hv,rfl⟩,rfl⟩
    change Metric.infDist (c • (v:E)) (V:Set E) ≤ t
    rw [infDist_submodule_smul, abs_of_pos hc.1]
    exact (mul_le_mul_of_nonneg_left hv hc.1.le).trans
      (mul_le_of_le_one_left ht.le hc.2.le)
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L k hd ht ht1).trans
  simp only [Real.rpow_natCast]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht.le _)
  calc
    (3:ℝ)^Module.finrank ℝ L.direction * 4^Module.finrank ℝ E ≤
        3^Module.finrank ℝ E * 4^Module.finrank ℝ E := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by exact_mod_cast (show (Module.finrank ℝ L.direction:ℝ) ≤ Module.finrank ℝ E by linarith))) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

lemma sphereLaw_rowProjection {r : ℕ} (A : Fin r → E)
    (hr : Module.finrank ℝ (rowSpan A) = r)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    sphereLaw {v : Metric.sphere (0:E) 1 | ‖rowProjectionL A (v:E)‖ ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) := by
  simp only [rowProjectionL_infDist]
  apply sphereLaw_submodule_tube (rowSpan A)ᗮ r _ ht ht1
  have h := (rowSpan A).finrank_add_finrank_orthogonal
  omega

end SphereTubes



section KernelSmallBall
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [nontrivialE : Nontrivial E]

omit nontrivialE in
lemma measurable_rowProjection_pair (r : ℕ) :
    Measurable (fun z : (Fin r → E) × E => rowProjectionL z.1 z.2) := by
  have he : Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact he.measurable.comp ((measurable_rowProjectionL r).comp measurable_fst |>.prodMk measurable_snd)


lemma gaussian_rowProjection_smallBall {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (v : E) (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin r => stdGaussian E) {A | ‖rowProjectionL A v‖ ≤ t} ≤
      ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) := by
  let G : Measure (Fin r → E) := Measure.pi fun _ => stdGaussian E
  let T : Set ((Fin r → E) × Metric.sphere (0:E) 1) :=
    {z | ‖rowProjectionL z.1 (z.2:E)‖ ≤ t}
  have hT : MeasurableSet T := measurableSet_le
    ((measurable_rowProjection_pair r).comp (measurable_fst.prodMk
      (measurable_subtype_coe.comp measurable_snd))).norm measurable_const
  have hconst : ∀ w : Metric.sphere (0:E) 1,
      G ((fun A => (A,w)) ⁻¹' T) = G {A | ‖rowProjectionL A v‖ ≤ t} := by
    intro w
    exact rowProjection_smallBall_eq (w:E) v ((mem_sphere_zero_iff_norm.mp w.property).trans hv.symm) t
  have heq : G.prod sphereLaw T = G {A | ‖rowProjectionL A v‖ ≤ t} := by
    rw [Measure.prod_apply_symm hT]
    simp only [hconst, lintegral_const, measure_univ, mul_one]
  rw [← heq, Measure.prod_apply hT]
  calc
    _ ≤ ∫⁻ _ : Fin r → E, ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * t^r) ∂G := by
      apply lintegral_mono_ae
      filter_upwards [gaussianRows_ae_rowSpan_finrank r hr] with A hA
      exact sphereLaw_rowProjection A hA ht ht1
    _ = _ := by simp

end KernelSmallBall



section ProjectionWitness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_unit_sphere_net {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ s : Finset E, (∀ v ∈ s, ‖v‖ = 1) ∧
      (s.card:ℝ) ≤ (3/t)^Module.finrank ℝ E ∧
      ∀ v:E, ‖v‖=1 → ∃ w ∈ s, dist v w ≤ t := by
  classical
  have hbound : ∀ s : Finset E, (∀ v ∈ s, ‖v‖ = 1) →
      (∀ v ∈ s, ∀ w ∈ s, v ≠ w → t < dist v w) →
      (s.card:ℝ) ≤ (3/t)^Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s ht zero_le_one (fun v hv => (hs v hv).le)
      (fun v hv w hw hne => (hsep v hv w hw hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < t/2) ht).mpr
    nlinarith
  obtain ⟨s,hs,hsep,hnet⟩ := exists_net_of_finite_packing_bound
    {v:E | ‖v‖=1} ht.le ⌈(3/t)^Module.finrank ℝ E⌉₊ (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s,hs,hbound s hs hsep,hnet⟩


omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_unit_projection_le_distance (P R : Submodule ℝ E) (hP : P ≠ ⊥)
    (u:E) (hu : ‖u‖=1) (huR : u ∈ Rᗮ) :
    ∃ v : P, ‖v‖=1 ∧ ‖R.starProjection (v:E)‖ ≤ Metric.infDist u (P:Set E) := by
  by_cases hp : P.starProjection u = 0
  · obtain ⟨w,hw,hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    let v : P := ⟨‖w‖⁻¹ • w,P.smul_mem _ hw⟩
    have hv : ‖v‖=1 := by
      change ‖‖w‖⁻¹ • w‖=1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
    refine ⟨v,hv,?_⟩
    rw [infDist_eq_norm_sub_projection, hp, sub_zero, hu]
    exact (R.norm_starProjection_apply_le (v:E)).trans_eq hv
  · let p := P.starProjection u
    let v : P := ⟨‖p‖⁻¹ • p,P.smul_mem _ (P.starProjection_apply_mem u)⟩
    have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hv : ‖v‖=1 := by
      change ‖‖p‖⁻¹ • p‖=1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0), inv_mul_cancel₀ hp0.ne']
    have hip : ⟪u,p⟫ = ‖p‖^2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact (P.inner_starProjection_left_eq_right u p).trans (by
        rw [P.starProjection_eq_self_iff.mpr (P.starProjection_apply_mem u)]) |>.symm
    have hiv : ⟪u,(v:E)⟫ = ‖p‖ := by
      change ⟪u, ‖p‖⁻¹ • p⟫ = ‖p‖
      rw [real_inner_smul_right, hip]
      field_simp
    have hic : ⟪u,Rᗮ.starProjection (v:E)⟫ = ‖p‖ := by
      rw [← Rᗮ.inner_starProjection_left_eq_right, (Rᗮ.starProjection_eq_self_iff.mpr huR)]
      exact hiv
    have hcs : ‖p‖ ≤ ‖Rᗮ.starProjection (v:E)‖ := by
      have h := real_inner_le_norm u (Rᗮ.starProjection (v:E))
      rwa [hic,hu,one_mul] at h
    have ht := Submodule.norm_sq_eq_add_norm_sq_starProjection (v:E) R
    have hpyt := Submodule.norm_sq_eq_add_norm_sq_starProjection u P
    have hdist : Metric.infDist u (P:Set E) = ‖Pᗮ.starProjection u‖ := by
      rw [infDist_eq_norm_sub_projection, Submodule.starProjection_orthogonal_val]
    refine ⟨v,hv,?_⟩
    rw [hdist]
    change ‖(v:E)‖=1 at hv
    rw [hv] at ht
    rw [hu] at hpyt
    have hs := sq_le_sq₀ (norm_nonneg p) (norm_nonneg (Rᗮ.starProjection (v:E))) |>.mpr hcs
    dsimp only [p] at hs
    nlinarith [norm_nonneg (Pᗮ.starProjection u), norm_nonneg (R.starProjection (v:E))]

end ProjectionWitness



section KernelSelectedSmallBall
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma kernel_selected_smallBall_raw {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (P : Submodule ℝ E) (hP : P ≠ ⊥)
    (Q : Measure ((Fin r → E) × E))
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1/2) :
    Q {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤
      ENNReal.ofReal ((3/t)^Module.finrank ℝ P *
        ((12:ℝ)^Module.finrank ℝ E * (2*t)^r)) := by
  classical
  obtain ⟨s,hs,hcard,hnet⟩ := exists_unit_sphere_net (E:=P) ht (by linarith)
  let T : P → Set (Fin r → E) := fun w => {A | ‖rowProjectionL A (w:E)‖ ≤ 2*t}
  have hTm : ∀ w, MeasurableSet (T w) := fun w =>
    measurableSet_le ((measurable_rowProjectionL r).apply_continuousLinearMap (w:E)).norm measurable_const
  have hUnion : MeasurableSet (⋃ w ∈ s, T w) :=
    s.finite_toSet.measurableSet_biUnion (fun w _ => hTm w)
  have hsub : {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤ᵐ[Q]
      Prod.fst ⁻¹' (⋃ w ∈ s, T w) := by
    filter_upwards [hsupport] with z hz
    intro hzt
    obtain ⟨v,hv,hvp⟩ := exists_unit_projection_le_distance P (rowSpan z.1) hP z.2 hz.1 hz.2
    obtain ⟨w,hw,hvw⟩ := hnet v hv
    refine Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨hw,?_⟩⟩)
    change ‖rowProjectionL z.1 (w:E)‖ ≤ 2*t
    have hdist : ‖(w:E)-(v:E)‖ ≤ t := by
      rw [dist_eq_norm] at hvw
      change ‖(w-v:P)‖ ≤ t
      simpa only [norm_sub_rev] using hvw
    have hproj : ‖rowProjectionL z.1 (v:E)‖ ≤ t := by
      rw [rowProjectionL_eq]
      exact hvp.trans hzt
    calc
      ‖rowProjectionL z.1 (w:E)‖ ≤ ‖rowProjectionL z.1 (v:E)‖ +
          ‖rowProjectionL z.1 ((w:E)-(v:E))‖ := by
        rw [map_sub]
        exact norm_le_insert' _ _
      _ ≤ t+t := add_le_add hproj ((rowProjectionL_contraction z.1 _).trans hdist)
      _ = 2*t := by ring
  calc
    Q {z | Metric.infDist z.2 (P:Set E) ≤ t} ≤ Q (Prod.fst ⁻¹' (⋃ w ∈ s, T w)) :=
      measure_mono_ae hsub
    _ = (Measure.pi fun _:Fin r => stdGaussian E) (⋃ w ∈ s, T w) := by
      rw [←Measure.fst_apply hUnion,hQ]
    _ ≤ ∑ w ∈ s, (Measure.pi fun _:Fin r => stdGaussian E) (T w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ s, ENNReal.ofReal ((12:ℝ)^Module.finrank ℝ E * (2*t)^r) := by
      exact Finset.sum_le_sum fun w hw => gaussian_rowProjection_smallBall hr (w:E)
        (hs w hw) (by positivity) (by linarith)
    _ = ENNReal.ofReal ((s.card:ℝ)*((12:ℝ)^Module.finrank ℝ E*(2*t)^r)) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))

end KernelSelectedSmallBall



def kernelSmallBallConstant : ℝ := 12^17

lemma kernelSmallBallConstant_ge_two : 2 ≤ kernelSmallBallConstant := by
  norm_num [kernelSmallBallConstant]

lemma kernelSmallBall_coefficient {d r p : ℕ} (hd : d ≤ 8*r) (hp : 2*p ≤ r)
    {t : ℝ} (ht : 0 < t) :
    (3/t)^p * ((12:ℝ)^d * (2*t)^r) ≤
      (kernelSmallBallConstant*t)^(r-p) := by
  have hpr : p ≤ r := by omega
  have hr : r ≤ 2*(r-p) := by omega
  have hpp : p ≤ r-p := by omega
  have hdd : d ≤ 16*(r-p) := by omega
  have hcoef : (3:ℝ)^p * 12^d * 2^r ≤ kernelSmallBallConstant^(r-p) := by
    calc
      (3:ℝ)^p*12^d*2^r ≤ 3^(r-p)*12^(16*(r-p))*2^(2*(r-p)) := by
        apply mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) hpp)
          (pow_le_pow_right₀ (by norm_num) hdd) (by positivity) (by positivity))
          (pow_le_pow_right₀ (by norm_num) hr) (by positivity) (by positivity)
      _ = _ := by
        rw [pow_mul, pow_mul, ←mul_pow, ←mul_pow]
        congr 1
        norm_num [kernelSmallBallConstant]
  have htPow : t^r = t^(r-p)*t^p := by
    rw [←pow_add, Nat.sub_add_cancel hpr]
  calc
    (3/t)^p * ((12:ℝ)^d*(2*t)^r) = (3^p*12^d*2^r)*t^(r-p) := by
      rw [div_pow, mul_pow, htPow]
      field_simp
    _ ≤ kernelSmallBallConstant^(r-p)*t^(r-p) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := (mul_pow _ _ _).symm



section KernelInverseOneStep
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma kernel_selected_scaled_smallBall {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (P : Submodule ℝ E)
    (hp : 2*Module.finrank ℝ P ≤ r) (hmargin : 2 ≤ r-Module.finrank ℝ P)
    (Q : Measure ((Fin r → E) × E))
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    {s:ℝ} (hs : 0<s) (hs1 : s≤1) :
    Q {z | kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} ≤
      ENNReal.ofReal (s^2) := by
  have hC := kernelSmallBallConstant_ge_two
  have hC0 : 0 < kernelSmallBallConstant := by linarith
  by_cases hP : P=⊥
  · have hz : Q {z | kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hsupport] with z hz
      rw [hP, infDist_eq_norm_sub_projection]
      simpa only [Submodule.starProjection_bot, zero_apply, sub_zero, hz.1,
        mul_one] using (show ¬kernelSmallBallConstant ≤ s by linarith)
    rw [hz]
    exact bot_le
  · have ht0 : 0 < s/kernelSmallBallConstant := div_pos hs hC0
    have ht1 : s/kernelSmallBallConstant ≤ 1/2 := by
      apply (div_le_iff₀ hC0).mpr
      linarith
    have heq : {z : (Fin r → E) × E |
        kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s} =
        {z | Metric.infDist z.2 (P:Set E) ≤ s/kernelSmallBallConstant} := by
      ext z
      change kernelSmallBallConstant * Metric.infDist z.2 (P:Set E) ≤ s ↔
        Metric.infDist z.2 (P:Set E) ≤ s/kernelSmallBallConstant
      rw [le_div_iff₀ hC0, mul_comm]
    rw [heq]
    apply (kernel_selected_smallBall_raw hr P hP Q hQ hsupport ht0 ht1).trans
    apply (ENNReal.ofReal_le_ofReal (kernelSmallBall_coefficient hd hp ht0)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_cancel₀ _ hC0.ne']
    exact pow_le_pow_of_le_one hs.le hs1 hmargin

end KernelInverseOneStep

section GenericInverseStep
variable {X : Type*} [MeasurableSpace X]

lemma inverse_moment_of_scaled_smallBall (Q : Measure X) [IsProbabilityMeasure Q]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {C : ℝ} (hC : 0<C)
    (htube : ∀ s:ℝ, 0<s → s≤1 → Q {x | C*f x ≤ s} ≤ ENNReal.ofReal (s^2)) :
    (∫⁻ x, ENNReal.ofReal ((f x)⁻¹) ∂Q) ≤ ENNReal.ofReal (5*C) ∧
      ∀ᵐ x ∂Q, 0 < f x := by
  have hm : (∫⁻ x, ENNReal.ofReal ((C*f x)⁻¹) ∂Q) ≤ 5 := by
    have h := inverse_moment_of_tube_bound Q (fun x => C*f x) 1
      (measurable_const.mul hf) (fun x => mul_nonneg hC.le (hf0 x)) 1 (by
        intro s hs hs1
        simpa only [one_mul] using htube s hs hs1)
    norm_num at h ⊢
    exact h
  have heq (x:X) : (f x)⁻¹ = C*(C*f x)⁻¹ := by
    rw [mul_inv, ←mul_assoc, mul_inv_cancel₀ hC.ne',one_mul]
  constructor
  · calc
      (∫⁻ x, ENNReal.ofReal ((f x)⁻¹) ∂Q) =
          ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ((C*f x)⁻¹) ∂Q := by
        simp_rw [heq, ENNReal.ofReal_mul hC.le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * 5 := mul_le_mul' le_rfl hm
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]; norm_num; ring
  · have hn : Q {x | f x = 0} = 0 := by
      have hb (n:ℕ) : Q {x | f x=0} ≤ ENNReal.ofReal (((1/2:ℝ)^n)^2) := by
        calc
          Q {x | f x=0} ≤ Q {x | C*f x ≤ (1/2:ℝ)^n} := by
            apply measure_mono
            intro x hx
            simp only [Set.mem_ofPred_eq] at hx ⊢
            rw [hx,mul_zero]
            positivity
          _ ≤ _ := htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      have hl : Tendsto (fun n:ℕ => ENNReal.ofReal (((1/2:ℝ)^n)^2)) atTop (𝓝 0) := by
        convert ENNReal.tendsto_ofReal ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).pow 2) using 1
        simp
      exact le_antisymm (ge_of_tendsto' hl hb) bot_le
    have ha : ∀ᵐ x ∂Q, f x ≠ 0 := by
      rw [ae_iff]
      simpa only [not_not] using hn
    filter_upwards [ha] with x hx
    exact lt_of_le_of_ne (hf0 x) hx.symm

end GenericInverseStep

section KernelInverseStepFinal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]


lemma kernel_selected_inverse_step {r : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (P : Submodule ℝ E)
    (hp : 2*Module.finrank ℝ P ≤ r) (hmargin : 2 ≤ r-Module.finrank ℝ P)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hQ : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ z, ENNReal.ofReal ((Metric.infDist z.2 (P:Set E))⁻¹) ∂Q) ≤
        ENNReal.ofReal (5*kernelSmallBallConstant) ∧
      ∀ᵐ z ∂Q, 0 < Metric.infDist z.2 (P:Set E) := by
  apply inverse_moment_of_scaled_smallBall Q (fun z => Metric.infDist z.2 (P:Set E))
    ((Metric.continuous_infDist_pt _).measurable.comp measurable_snd)
    (fun _ => Metric.infDist_nonneg) (by have := kernelSmallBallConstant_ge_two; linarith)
  exact fun s hs hs1 => kernel_selected_scaled_smallBall hr hd P hp hmargin Q hQ hsupport hs hs1

end KernelInverseStepFinal




end CurrentProjection

end

end OAI
