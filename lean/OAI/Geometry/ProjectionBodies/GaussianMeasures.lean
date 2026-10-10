import OAI.Geometry.ProjectionBodies.Brouwer

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

/-- The actual one-dimensional radial Gaussian moment. -/
def gaussianRadial (d : ℕ) : ℝ := ∫ r in Ioi (0:ℝ),r^d*Real.exp (-(r^2))

lemma gaussianRadial_eq (d : ℕ) : gaussianRadial d=(1/2:ℝ)*Real.Gamma (((d:ℝ)+1)/2) := by
  simpa only [gaussianRadial,Real.rpow_natCast,Real.rpow_two] using
    integral_rpow_mul_exp_neg_rpow (p := (2:ℝ)) (q := (d:ℝ)) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])

lemma gaussianRadial_pos (d : ℕ) : 0<gaussianRadial d := by
  rw [gaussianRadial_eq]
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by positivity))

lemma gaussianRadial_add_two (d : ℕ) :
    gaussianRadial (d+2)=((d:ℝ)+1)/2*gaussianRadial d := by
  rw [gaussianRadial_eq,gaussianRadial_eq]
  have he : (((d+2:ℕ):ℝ)+1)/2=((d:ℝ)+1)/2+1 := by push_cast;ring
  rw [he,Real.Gamma_add_one (by positivity)]
  ring

lemma integral_radial_gaussian (m k : ℕ) :
    (∫ r : Ioi (0:ℝ),r.val^k*Real.exp (-(r.val^2)) ∂Measure.volumeIoiPow m)=gaussianRadial (m+k) := by
  simp only [Measure.volumeIoiPow,ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => (r^m).toNNReal • (r^k*Real.exp (-(r^2))))]
    unfold gaussianRadial
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [NNReal.smul_def,Real.coe_toNNReal _ (pow_nonneg hx.le _),pow_add]
    ring
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma surface_integral_eq_mean {n : ℕ} [NeZero n] (f : Sphere n → ℝ) :
    (∫ u,f u ∂surface n)=(n:ℝ)*kappa n*mean f := by
  rw [mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _=(n:ℝ)*kappa n*(((surface n).real univ)⁻¹* _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

/-- Polar separation for any positively homogeneous integrand. No smoothness
or differentiability is used, and the Bochner integral has its ordinary meaning. -/
lemma homogeneous_gaussian_integral {n : ℕ} [NeZero n] (k : ℕ) (f : Space n → ℝ)
    (hh : ∀ r : ℝ,0<r → ∀ x,f (r • x)=r^k*f x) :
    (∫ x,f x*Real.exp (-(‖x‖^2)))=
      (n:ℝ)*kappa n*mean (fun u : Sphere n => f u)*gaussianRadial (n-1+k) := by
  let F : Space n → ℝ := fun x => f x*Real.exp (-(‖x‖^2))
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  have he : (∫ x,F x)=∫ x : ({0}ᶜ : Set (Space n)),F x ∂volume.comap Subtype.val := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
  rw [show (∫ x,f x*Real.exp (-(‖x‖^2)))=∫ x,F x from rfl,he]
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  rw [← (hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv).integral_comp
    (homeomorphUnitSphereProd (Space n)).symm.measurableEmbedding (fun x => F x)]
  have hfun : (fun z : Sphere n × Ioi (0:ℝ) => F ↑((homeomorphUnitSphereProd (Space n)).symm z))=
      (fun z => f z.1*(z.2.val^k*Real.exp (-(z.2.val^2)))) := by
    funext z
    rw [homeomorphUnitSphereProd_symm_apply_coe]
    dsimp only [F]
    rw [hh _ z.2.property,norm_smul,Real.norm_of_nonneg z.2.property.le,norm_coe,mul_one]
    ring
  change (∫ z : Sphere n × Ioi (0:ℝ),F ↑((homeomorphUnitSphereProd (Space n)).symm z) ∂(surface n).prod ν)=_
  rw [hfun]
  rw [integral_prod_mul (fun u : Sphere n => f u) (fun r : Ioi (0:ℝ) => r.val^k*Real.exp (-(r.val^2))),
    surface_integral_eq_mean]
  dsimp only [ν]
  rw [integral_radial_gaussian]
  simp only [finrank_euclideanSpace_fin]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection
variable {n : ℕ}

lemma norm_integrable_map {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (A : Space n →L[ℝ] Space n) :
    Integrable (fun x : Space n => ‖x‖) (μ.map A) := by
  apply (integrable_map_measure continuous_norm.aestronglyMeasurable A.continuous.measurable.aemeasurable).mpr
  exact (hμ.const_mul ‖A‖).mono' (continuous_norm.comp A.continuous).aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_norm] using A.le_opNorm x))

lemma cosine_map (μ : Measure (Space n)) (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (A : Space n →L[ℝ] Space n) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x=cosineSeminorm μ hμ (A.adjoint x) := by
  change (∫ y,|⟪y,x⟫| ∂μ.map A)=∫ y,|⟪y,A.adjoint x⟫| ∂μ
  rw [integral_map A.continuous.measurable.aemeasurable (by fun_prop)]
  congr 1
  funext y
  rw [ContinuousLinearMap.adjoint_inner_right]

lemma adjoint_ne_zero_on_range (A : Space n →L[ℝ] Space n) {x : Space n}
    (hx : x∈LinearMap.range A.toLinearMap) (hx0 : x≠0) : A.adjoint x≠0 := by
  intro h
  obtain ⟨y,rfl⟩ := hx
  change A.adjoint (A y)=0 at h
  change A y≠0 at hx0
  have hh := ContinuousLinearMap.adjoint_inner_right A y (A y)
  rw [h,inner_zero_right,real_inner_self_eq_norm_sq] at hh
  exact hx0 (norm_eq_zero.mp (by nlinarith [norm_nonneg (A y)]))

lemma cosine_map_pos {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x)
    (A : Space n →L[ℝ] Space n) (x : Space n)
    (hx : x∈LinearMap.range A.toLinearMap) (hx0 : x≠0) :
    0<cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x := by
  rw [cosine_map]
  exact hq _ (adjoint_ne_zero_on_range A hx hx0)

lemma functional_map {μ : Measure (Space n)} (A : Space n →L[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) :
    supportFunctional (μ.map A) K=∫ x,support K (A x) ∂μ := by
  exact integral_map A.continuous.measurable.aemeasurable (support_continuous hK).aestronglyMeasurable

lemma cosine_map_projection {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (A : Space n →L[ℝ] Space n) (x : Space n) :
    cosineSeminorm (μ.map A) (norm_integrable_map hμ A)
      ((LinearMap.range A.toLinearMap).starProjection x)=
        cosineSeminorm (μ.map A) (norm_integrable_map hμ A) x := by
  change (∫ y,|⟪y,(LinearMap.range A.toLinearMap).starProjection x⟫| ∂μ.map A)=∫ y,|⟪y,x⟫| ∂μ.map A
  rw [integral_map A.continuous.measurable.aemeasurable (by fun_prop),
    integral_map A.continuous.measurable.aemeasurable (by fun_prop)]
  congr 1
  funext y
  rw [← Submodule.inner_starProjection_left_eq_right,
    (LinearMap.range A.toLinearMap).starProjection_eq_self_iff.mpr
      (show A y∈LinearMap.range A.toLinearMap from ⟨y,rfl⟩)]

lemma functional_map_continuous {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (fun A : Space n →L[ℝ] Space n => supportFunctional (μ.map A) K) := by
  simp_rw [functional_map _ hK]
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hlip := support_lipschitz hK hne (R := ⟨R,hR.le⟩) hbound
  apply continuous_iff_continuousAt.mpr
  intro A
  apply continuousAt_of_dominated (bound := fun x => R*(‖A‖+1)*‖x‖) <;> try infer_instance
  · filter_upwards [] with B
    exact (support_continuous hK).aestronglyMeasurable.comp_measurable B.continuous.measurable
  · filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (show ‖A‖<‖A‖+1 by linarith))] with B hB
    filter_upwards [] with x
    have hz : support K 0=0 := by
      obtain ⟨z,hz,he⟩ := support_attained hK hne 0
      simpa only [inner_zero_left] using he
    have hh := hlip.norm_sub_le (B x) 0
    rw [hz,sub_zero,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (B.le_opNorm x) hR.le).trans
      (by
        calc
          R*(‖B‖*‖x‖) ≤ R*((‖A‖+1)*‖x‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)) hR.le
          _ = R*(‖A‖+1)*‖x‖ := by ring))
  · exact hμ.const_mul (R*(‖A‖+1))
  · filter_upwards [] with x
    exact ((support_continuous hK).comp (by fun_prop : Continuous (fun B : Space n →L[ℝ] Space n => B x))).continuousAt

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (seminorm_continuous)
variable {n : ℕ}

def projectedUnit (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) : Set (Space n) :=
  closure (V.starProjection '' seminormUnit g)

lemma projectedUnit_sub (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    projectedUnit V g⊆V := by
  apply closure_minimal _ V.closed_of_finiteDimensional
  rintro _ ⟨x,_,rfl⟩
  exact V.starProjection_apply_mem x

lemma projectedUnit_convex (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    Convex ℝ (projectedUnit V g) := (seminormUnit_convex g).linear_image V.starProjection.toLinearMap |>.closure

lemma projectedUnit_balanced (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    Balanced ℝ (projectedUnit V g) := by
  apply Balanced.closure
  intro a ha y hy
  obtain ⟨z,⟨w,hw,rfl⟩,rfl⟩ := hy
  refine ⟨a • w,(seminormUnit_balanced g) a ha ⟨w,hw,rfl⟩,?_⟩
  exact map_smul V.starProjection a w

lemma projectedUnit_inner (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n)) :
    ∃ r : ℝ,0<r ∧ ∀ x∈V,‖x‖≤r → x∈projectedUnit V g := by
  obtain ⟨r,hr,hin⟩ := Metric.mem_nhds_iff.mp (seminormUnit_nhds g)
  refine ⟨r/2,by positivity,fun x hx hn => subset_closure ⟨x,hin ?_,?_⟩⟩
  · rw [mem_ball,dist_zero_right]; linarith
  · exact V.starProjection_eq_self_iff.mpr hx

lemma projectedUnit_compact (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) :
    IsCompact (projectedUnit V g) := by
  apply (isCompact_closedBall (0:Space n) c⁻¹).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  rintro _ ⟨x,hx,rfl⟩
  rw [mem_closedBall,dist_zero_right,inv_eq_one_div,le_div_iff₀ hc]
  change g x≤1 at hx
  nlinarith [hl x]

namespace RelativeGauge
variable {V : Submodule ℝ (Space n)}

def project (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) : RelativeGauge V :=
  ofBody (projectedUnit_compact V g hc hl) (projectedUnit_convex V g)
    (projectedUnit_balanced V g) (projectedUnit_inner V g)

lemma project_body (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) :
    (project V g hc hl).body=projectedUnit V g :=
  body_ofBody _ _ _ (projectedUnit_sub V g) _

lemma project_le (V : Submodule ℝ (Space n)) (g : Seminorm ℝ (Space n))
    {c : ℝ} (hc : 0<c) (hl : ∀ x,c*‖V.starProjection x‖≤g x) (x : Space n) :
    project V g hc hl x≤g x := by
  change gauge (V.starProjection ⁻¹' projectedUnit V g) x≤g x
  rw [← gauge_seminormUnit g x]
  apply gauge_mono (absorbent_nhds_zero (seminormUnit_nhds g))
  intro y hy
  exact subset_closure ⟨y,hy,rfl⟩

lemma support_cylinder_bound (g : RelativeGauge V) (u : Space n) (hu : u∈V) (z : Space n) :
    ⟪u,z⟫ / max 1 (g z) ≤ support g.body u := by
  have ha : 0 < max 1 (g z) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let y := (max 1 (g z))⁻¹ • V.starProjection z
  have hy : y∈g.body := by
    refine ⟨V.smul_mem _ (V.starProjection_apply_mem z),?_⟩
    change g.toSeminorm ((max 1 (g z))⁻¹ • V.starProjection z)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr ha.le),inv_mul_le_iff₀ ha,mul_one]
    change g (V.starProjection z)≤ max 1 (g z)
    rw [g.projection]
    exact le_max_right _ _
  have hh := inner_le_support g.compact hy u
  dsimp only [y] at hh
  rw [inner_smul_right,← Submodule.inner_starProjection_left_eq_right,
    V.starProjection_eq_self_iff.mpr hu] at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

end RelativeGauge
end PettyProjection
end

end OAI
