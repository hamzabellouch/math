import OAI.Geometry.ProjectionBodies.NormRigidity

namespace OAI

universe uα uι

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma seminorm_le_max_norm {n : ℕ} (g : Seminorm ℝ (Space n)) {R : ℝ}
    (hmax : ∀ u : Sphere n, g u ≤ R) (x : Space n) : g x ≤ R*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by simp [norm_smul,hx0]⟩
  have hu := hmax u
  have hgu : g x=‖x‖*g u := by
    change g x=‖x‖*g (‖x‖⁻¹ • x)
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    field_simp
  rw [hgu]
  nlinarith [norm_nonneg x]

/-- Exact coordinate minorant used for logarithmic coercivity and continuous
extension to singular matrix ranks. -/
lemma seminorm_coordinate_minorant {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n))
    (hg : g ≠ 0) : ∃ (R : ℝ) (e : Sphere n), 0 < R ∧
      (∀ u : Sphere n, g u ≤ R) ∧
      (∀ x : Space n, R*|⟪x,(e:Space n)⟫| ≤ g x) := by
  have hne : (sphere (0 : Space n) 1).Nonempty := by
    obtain ⟨x,hx⟩ := exists_norm_eq (Space n) (by norm_num : (0:ℝ)≤1)
    exact ⟨x,by simpa [mem_sphere,dist_zero_right]⟩
  obtain ⟨v,hv,hm⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn hne
    (seminorm_continuous n g).continuousOn
  have hv1 : ‖v‖=1 := by simpa [mem_sphere,dist_zero_right] using hv
  let R := g v
  have hR : 0≤R := apply_nonneg g v
  have hmax (u : Sphere n) : g u ≤ R := hm u.property
  have hbound := seminorm_le_max_norm g hmax
  have hRp : 0<R := by
    by_contra h
    have hz : R=0 := le_antisymm (le_of_not_gt h) hR
    apply hg
    ext x
    exact le_antisymm (by simpa [hz] using hbound x) (apply_nonneg g x)
  let S := Submodule.span ℝ {v}
  let f : Module.Dual ℝ S := R • ((innerSL ℝ v).toLinearMap.comp S.subtype)
  have hf (y : S) : |f y| ≤ g (y:Space n) := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp y.property
    change |R*⟪v,(y:Space n)⟫| ≤ g (y:Space n)
    rw [← ha,inner_smul_right,real_inner_self_eq_norm_sq,hv1,map_smul_eq_mul]
    simp only [one_pow,mul_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg hR]
    dsimp only [R]
    rw [mul_comm]
  obtain ⟨φ,hφ,hφbound⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
    S f (seminorm_continuous n g) (fun y => (le_abs_self _).trans (hf y))
  have hφv : φ v=R := by
    have h := hφ ⟨v,Submodule.mem_span_singleton_self v⟩
    simpa [f,real_inner_self_eq_norm_sq,hv1] using h
  have hφnorm : ‖φ‖=R := by
    apply le_antisymm
    · exact φ.opNorm_le_bound hR (fun x => by simpa only [Real.norm_eq_abs] using (hφbound x).trans (hbound x))
    · have h := φ.le_opNorm v
      rw [hφv,hv1,Real.norm_of_nonneg hR,mul_one] at h
      exact h
  let w := (InnerProductSpace.toDual ℝ (Space n)).symm φ
  have hw : ‖w‖=R := by simpa only [w,LinearIsometryEquiv.norm_map] using hφnorm
  let e : Sphere n := ⟨R⁻¹ • w,by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR),hw]
    exact inv_mul_cancel₀ hRp.ne'⟩
  refine ⟨R,e,hRp,hmax,fun x => ?_⟩
  change R*|⟪x,R⁻¹ • w⟫| ≤ g x
  rw [inner_smul_right,abs_mul,abs_of_pos (inv_pos.mpr hRp),← mul_assoc,
    mul_inv_cancel₀ hRp.ne',one_mul,real_inner_comm]
  simpa only [w,InnerProductSpace.toDual_symm_apply] using hφbound x

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma intervalIntegrable_abs_rpow {p a b : ℝ} (hp : -1<p) :
    IntervalIntegrable (fun t : ℝ => |t|^p) volume a b := by
  apply intervalIntegrable_of_even (fun t => by rw [abs_neg])
  intro x hx
  apply (intervalIntegral.intervalIntegrable_rpow' hp).congr
  intro t ht
  rw [uIoc_of_le hx.le] at ht
  dsimp only
  rw [abs_of_nonneg ht.1.le]

lemma inner_rpow_integrable_ball {n : ℕ} (e : Sphere n) {p : ℝ} (hp : -1<p) :
    IntegrableOn (fun x : Space n => |⟪(e:Space n),x⟫|^p) (ball 0 1) := by
  let B := ball (0 : perpendicular (e:Space n)) 1
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isBounded_ball : Bornology.IsBounded B).measure_lt_top⟩
  have hI : Integrable (fun z : perpendicular (e:Space n) × ℝ => |z.2|^p)
      ((volume.restrict B).prod (volume.restrict (Icc (-1:ℝ) 1))) := by
    have h := (integrableOn_Icc_iff_integrableOn_Ioc (f := fun t : ℝ => |t|^p)).mpr
      (intervalIntegrable_abs_rpow (a := -1) (b := 1) hp).1
    exact h.comp_snd _
  rw [Measure.prod_restrict,← Measure.volume_eq_prod] at hI
  have hsub : (shadowMeasurableEquiv e) ⁻¹' ball (0:Space n) 1 ⊆ B ×ˢ Icc (-1:ℝ) 1 := by
    rintro ⟨z,t⟩ h
    have hnorm : ‖shadowCoords e (WithLp.toLp 2 (z,t))‖<1 := by
      simpa [shadowMeasurableEquiv] using h
    rw [(shadowCoords e).norm_map] at hnorm
    have hz := WithLp.norm_fst_le (p := (2:ℝ≥0∞)) _ (WithLp.toLp 2 (z,t))
    have ht := WithLp.norm_snd_le (p := (2:ℝ≥0∞)) _ (WithLp.toLp 2 (z,t))
    refine ⟨?_,?_⟩
    · simpa only [B,mem_ball,dist_zero_right,WithLp.toLp_fst] using hz.trans_lt hnorm
    · have habs : |t|<1 := by exact ht.trans_lt hnorm
      exact ⟨(neg_lt_of_abs_lt habs).le,(lt_of_abs_lt habs).le⟩
  change IntegrableOn (fun z : perpendicular (e:Space n) × ℝ => |z.2|^p) (B ×ˢ Icc (-1:ℝ) 1) at hI
  have hI' := hI.mono_set hsub
  have heq : (fun z : perpendicular (e:Space n) × ℝ => |⟪(e:Space n),shadowMeasurableEquiv e z⟫|^p)=
      (fun z => |z.2|^p) := by
    funext z
    change |⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫|^p=_
    rw [inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
    simp
  exact ((shadowMeasurableEquiv_measurePreserving e).integrableOn_comp_preimage
    (shadowMeasurableEquiv e).measurableEmbedding).mp (by simpa only [comp_def,heq] using hI')

lemma sphere_integrable_of_homogeneous {n : ℕ} [NeZero n] {f : Space n → ℝ} {p : ℝ}
    (hf : IntegrableOn f (ball 0 1))
    (hh : ∀ (r : ℝ),0<r → ∀ x,f (r • x)=r^p*f x) :
    Integrable (fun u : Sphere n => f u) (sigma n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let I : Set (Ioi (0:ℝ)) := Iio ⟨1,by norm_num⟩
  have hνI : ν I ≠ 0 := by
    have h := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n)-1)
      (⟨1,by norm_num⟩ : Ioi (0:ℝ))
    change ν I=_ at h
    rw [h]
    apply (ENNReal.ofReal_pos.mpr _).ne'
    positivity
  let F : Space n → ℝ := (ball (0:Space n) 1).indicator f
  have hF : Integrable F := hf.integrable_indicator measurableSet_ball
  have hs := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0:Space n)).compl).mp
    (hF.integrableOn (s := ({0}ᶜ : Set (Space n))))
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hprod := (hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv).integrable_comp_emb
    (homeomorphUnitSphereProd (Space n)).symm.measurableEmbedding |>.mpr hs
  have hAE : ∀ᵐ r ∂ν, Integrable (fun u : Sphere n => F (r.1 • (u:Space n))) (surface n) := by
    have h := hprod.prod_left_ae
    change ∀ᵐ r ∂ν, Integrable (fun u => F ↑((homeomorphUnitSphereProd (Space n)).symm (u,r))) (surface n) at h
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using h
  obtain ⟨r,hr,hir⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hνI (ae_restrict_of_ae hAE)
  have hr1 : (r:ℝ)<1 := hr
  have hp : r.1^p ≠ 0 := (Real.rpow_pos_of_pos r.property p).ne'
  have hfun : (fun u : Sphere n => F (r.1 • (u:Space n)))=(fun u : Sphere n => r.1^p*f u) := by
    funext u
    have hu : r.1 • (u:Space n) ∈ ball (0:Space n) 1 := by
      simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_of_nonneg r.property.le,norm_coe,mul_one] using hr1
    dsimp only [F]
    rw [indicator_of_mem hu,hh r r.property]
  rw [hfun] at hir
  have hi := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hp) (fun u : Sphere n => f u)).mp hir
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)))

lemma inner_rpow_integrable_sphere {n : ℕ} [NeZero n] (e : Sphere n) {p : ℝ} (hp : -1<p) :
    Integrable (fun u : Sphere n => |⟪(e:Space n),(u:Space n)⟫|^p) (sigma n) := by
  apply sphere_integrable_of_homogeneous (p := p) (inner_rpow_integrable_ball e hp)
  intro r hr x
  rw [inner_smul_right,abs_mul,abs_of_pos hr,Real.mul_rpow hr.le (abs_nonneg _)]

lemma log_sq_le_negative_rpow {t : ℝ} (ht : 0<t) (h1 : t≤1) :
    (Real.log t)^2 ≤ 16*t^(-(1/2:ℝ)) := by
  have hl : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.le h1)
  have h := Real.log_le_rpow_div (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ)<1/4)
  rw [Real.log_inv] at h
  have hsq := sq_le_sq₀ hl (by positivity : 0 ≤ (t⁻¹)^(1/4:ℝ)/(1/4:ℝ)) |>.mpr h
  have hp : ((t⁻¹)^(1/4:ℝ))^2=t^(-(1/2:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (inv_nonneg.mpr ht.le),Real.inv_rpow ht.le]
    norm_num
    rw [Real.rpow_neg ht.le]
  rw [div_pow,neg_sq, hp] at hsq
  norm_num at hsq
  nlinarith

lemma log_inner_sq_integrable {n : ℕ} [NeZero n] (e : Sphere n) :
    Integrable (fun u : Sphere n => (Real.log |⟪(e:Space n),(u:Space n)⟫|)^2) (sigma n) := by
  apply ((inner_rpow_integrable_sphere e (by norm_num : (-1:ℝ)< -(1/2:ℝ))).const_mul 16).mono'
    ((measurable_const.inner measurable_subtype_coe).abs.log.pow_const 2).aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  by_cases h : |⟪(e:Space n),(u:Space n)⟫|=0
  · simp only [h,Real.log_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    positivity
  · apply log_sq_le_negative_rpow (lt_of_le_of_ne (abs_nonneg _) (Ne.symm h))
    simpa only [norm_coe,mul_one] using (abs_real_inner_le_norm (e:Space n) (u:Space n))

lemma log_inner_integrable {n : ℕ} [NeZero n] (e : Sphere n) :
    Integrable (fun u : Sphere n => Real.log |⟪(e:Space n),(u:Space n)⟫|) (sigma n) := by
  apply ((log_inner_sq_integrable e).add (integrable_const (1:ℝ))).mono'
    ((measurable_const.inner measurable_subtype_coe).abs.log.aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs]
  let x := Real.log |⟪(e:Space n),(u:Space n)⟫|
  change |x| ≤ x^2+1
  nlinarith [sq_nonneg (|x|-1),sq_abs x]

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_ne_zero_ae_sphere {n : ℕ} (e : Sphere n) :
    ∀ᵐ (u : Sphere n) ∂sigma n, ⟪(e:Space n),(u:Space n)⟫ ≠ 0 := by
  apply sphere_ae_of_radial (P := fun x : Space n => ⟪(e:Space n),x⟫ ≠ 0)
  · have hR : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simpa only [ae_iff,not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton (0:ℝ))
    have hp : ∀ᵐ z : perpendicular (e:Space n) × ℝ ∂volume, z.2 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact (Measure.ae_prod_iff_ae_ae (by measurability)).mpr (Eventually.of_forall (fun _ => hR))
    have he : ∀ᵐ x : Space n ∂volume, ((shadowMeasurableEquiv e).symm x).2 ≠ 0 :=
      ((shadowMeasurableEquiv_measurePreserving e).symm (shadowMeasurableEquiv e)).quasiMeasurePreserving.ae hp
    filter_upwards [he] with x hx
    have hy := (shadowMeasurableEquiv e).apply_symm_apply x
    have hid (z : perpendicular (e:Space n) × ℝ) :
        ⟪(e:Space n),shadowMeasurableEquiv e z⟫=z.2 := by
      change ⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫=z.2
      rw [inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
      simp
    rwa [← hid,hy] at hx
  · intro u r _ h
    rw [inner_smul_right,mul_ne_zero_iff] at h
    exact h.2

lemma mean_inner_independent {n : ℕ} (f : ℝ → ℝ) (e v : Sphere n) :
    mean (fun u : Sphere n => f ⟪(e:Space n),(u:Space n)⟫) =
      mean (fun u : Sphere n => f ⟪(v:Space n),(u:Space n)⟫) := by
  let U := (ℝ ∙ ((e:Space n)-(v:Space n)))ᗮ.reflection
  have hev : U e=v := Submodule.reflection_sub ((norm_coe e).trans (norm_coe v).symm)
  have h := mean_rotation U (fun u : Sphere n => f ⟪U (e:Space n),(u:Space n)⟫)
  change mean (fun u : Sphere n => f ⟪U (e:Space n),U (u:Space n)⟫)=_ at h
  simp only [U.inner_map_map] at h
  simpa only [hev] using h

lemma seminorm_pos_ae_sphere {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    ∀ᵐ (u : Sphere n) ∂sigma n, 0 < g u := by
  obtain ⟨R,e,hR,_,hb⟩ := seminorm_coordinate_minorant g hg
  filter_upwards [inner_ne_zero_ae_sphere e] with u hu
  exact (mul_pos hR (abs_pos.mpr (by simpa only [real_inner_comm] using hu))).trans_le (hb u)

lemma log_sq_coercive_bound {a R t : ℝ} (ha : 0<a) (ha1 : a≤1) (hR : 0<R)
    (htl : R*a≤t) (htu : t≤R) :
    (Real.log t)^2 ≤ 2*(Real.log R)^2+2*(Real.log a)^2 := by
  have ht := (mul_pos hR ha).trans_le htl
  have hl0 := Real.log_le_log (mul_pos hR ha) htl
  rw [Real.log_mul hR.ne' ha.ne'] at hl0
  have hl1 := Real.log_le_log ht htu
  have ha0 : Real.log a≤0 := Real.log_nonpos ha.le ha1
  have habs : |Real.log t|≤|Real.log R|+|Real.log a| := by
    rw [abs_le]
    constructor
    · rw [abs_of_nonpos ha0]
      linarith [neg_abs_le (Real.log R)]
    · linarith [le_abs_self (Real.log R),abs_nonneg (Real.log a)]
  have hs := sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤|Real.log R|+|Real.log a|) |>.mpr habs
  nlinarith [sq_nonneg (|Real.log R|-|Real.log a|),sq_abs (Real.log R),sq_abs (Real.log a),sq_abs (Real.log t)]

lemma seminorm_log_sq_integrable {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    Integrable (fun u : Sphere n => (Real.log (g u))^2) (sigma n) := by
  obtain ⟨R,e,hR,hm,hb⟩ := seminorm_coordinate_minorant g hg
  apply ((integrable_const (2*(Real.log R)^2)).add ((log_inner_sq_integrable e).const_mul 2)).mono'
    (((seminorm_continuous n g).comp continuous_subtype_val).measurable.log.pow_const 2).aestronglyMeasurable
  filter_upwards [inner_ne_zero_ae_sphere e] with u hu
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply log_sq_coercive_bound (abs_pos.mpr hu) _ hR _ (hm u)
  · simpa only [norm_coe,mul_one] using abs_real_inner_le_norm (e:Space n) (u:Space n)
  · simpa only [real_inner_comm] using hb u

lemma seminorm_log_integrable {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)} (hg : g ≠ 0) :
    Integrable (fun u : Sphere n => Real.log (g u)) (sigma n) := by
  apply ((seminorm_log_sq_integrable hg).add (integrable_const (1:ℝ))).mono'
    (((seminorm_continuous n g).comp continuous_subtype_val).measurable.log.aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs]
  change |Real.log (g u)| ≤ (Real.log (g u))^2+1
  nlinarith [sq_nonneg (|Real.log (g u)|-1),sq_abs (Real.log (g u))]

lemma seminorm_log_coercivity {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)}
    {R : ℝ} {e : Sphere n} (hR : 0<R) (hg : g ≠ 0)
    (hb : ∀ x : Space n,R*|⟪x,(e:Space n)⟫|≤g x) :
    Real.log R+mean (fun u : Sphere n => Real.log |⟪(pole n:Space n),(u:Space n)⟫|) ≤
      mean (fun u : Sphere n => Real.log (g u)) := by
  have hi := integral_mono_ae ((integrable_const (Real.log R)).add (log_inner_integrable e))
    (seminorm_log_integrable hg) (by
      filter_upwards [inner_ne_zero_ae_sphere e] with u hu
      have h := hb u
      rw [real_inner_comm] at h
      simpa only [Pi.add_apply,Real.log_mul hR.ne' (abs_pos.mpr hu).ne'] using
        Real.log_le_log (mul_pos hR (abs_pos.mpr hu)) h)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (log_inner_integrable e),integral_const] at hi
  simp only [probReal_univ,one_smul] at hi
  change (Real.log R)+mean (fun u : Sphere n => Real.log |⟪(e:Space n),(u:Space n)⟫|)≤_ at hi
  rwa [mean_inner_independent (fun t => Real.log |t|) e (pole n)] at hi

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma unifIntegrable_of_sq_bound {α : Type uα} {ι : Type uι} [MeasurableSpace α] {μ : Measure α}
    {f : ι → α → ℝ} {C : ℝ} (hC : 0≤C)
    (hi : ∀ i,Integrable (f i) μ) (hsq : ∀ i,Integrable (fun x => (f i x)^2) μ)
    (hb : ∀ i,(∫ x,(f i x)^2 ∂μ)≤C) : UnifIntegrable f 1 μ := by
  apply unifIntegrable_of le_rfl (by norm_num) (fun i => (hi i).aestronglyMeasurable)
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact ⟨0, fun _ => hεtop.symm ▸ le_top⟩
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  rw [← ENNReal.ofReal_toReal hεtop]
  let M : ℝ := C/ε.toReal+1
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨⟨M,hM.le⟩,fun i => ?_⟩
  let T := {x | (⟨M,hM.le⟩ : ℝ≥0)≤‖f i x‖₊}
  have hind : Integrable (T.indicator (f i)) μ := (hi i).indicator₀
    (nullMeasurableSet_le aemeasurable_const (hi i).aestronglyMeasurable.aemeasurable.nnnorm)
  change eLpNorm (T.indicator (f i)) 1 μ ≤ ENNReal.ofReal ε.toReal
  rw [eLpNorm_one_eq_lintegral_enorm hind.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hind]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ x,(f i x)^2/M ∂μ := by
      apply integral_mono hind.norm ((hsq i).div_const M)
      intro x
      change ‖T.indicator (f i) x‖ ≤ (f i x)^2/M
      by_cases hx : x∈T
      · rw [indicator_of_mem hx,Real.norm_eq_abs]
        have hx' : M≤|f i x| := hx
        apply (le_div_iff₀ hM).mpr
        nlinarith [sq_abs (f i x)]
      · rw [indicator_of_notMem hx,norm_zero]
        positivity
    _ = (∫ x,(f i x)^2 ∂μ)/M := by simp only [div_eq_mul_inv,integral_mul_const]
    _ ≤ C/M := div_le_div_of_nonneg_right (hb i) hM.le
    _ ≤ ε.toReal := by
      apply (div_le_iff₀ hM).mpr
      dsimp [M]
      rw [mul_add,mul_div_cancel₀ _ hεreal.ne']
      linarith

lemma tendsto_integral_of_sq_bound {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ} {C : ℝ} (hC : 0≤C)
    (hi : ∀ i,Integrable (f i) μ) (hsq : ∀ i,Integrable (fun x => (f i x)^2) μ)
    (hb : ∀ i,(∫ x,(f i x)^2 ∂μ)≤C) (hg : Integrable g μ)
    (hc : ∀ᵐ x ∂μ,Tendsto (fun i => f i x) atTop (𝓝 (g x))) :
    Tendsto (fun i => ∫ x,f i x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
  apply tendsto_integral_of_L1' g (Eventually.of_forall hi)
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num)
    (fun i => (hi i).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg)
    (unifIntegrable_of_sq_bound hC hi hsq hb) hc

lemma seminorm_log_sq_bound {n : ℕ} [NeZero n] {g : Seminorm ℝ (Space n)}
    {r R : ℝ} (hr : 0<r) (hlo : ∃ u : Sphere n,r≤g u) (hhi : ∀ u : Sphere n,g u≤R) :
    mean (fun u : Sphere n => (Real.log (g u))^2) ≤
      2*(|Real.log r|+|Real.log R|)^2+
        2*mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2) := by
  have hg : g ≠ 0 := by
    rintro rfl
    obtain ⟨u,hu⟩ := hlo
    simpa using hr.not_ge hu
  obtain ⟨a,e,ha,hm,hb⟩ := seminorm_coordinate_minorant g hg
  have hla : r≤a := by obtain ⟨u,hu⟩ := hlo; exact hu.trans (hm u)
  have hha : a≤R := by
    have h := hb e
    rw [real_inner_self_eq_norm_sq,norm_coe] at h
    norm_num at h
    exact h.trans (hhi e)
  have hlogs : |Real.log a|≤|Real.log r|+|Real.log R| := by
    have h1 := Real.log_le_log hr hla
    have h2 := Real.log_le_log ha hha
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log r),abs_nonneg (Real.log R)]
    · linarith [le_abs_self (Real.log R),abs_nonneg (Real.log r)]
  have hlogs2 : (Real.log a)^2≤(|Real.log r|+|Real.log R|)^2 := by
    simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr hlogs
  have h := integral_mono_ae (seminorm_log_sq_integrable hg)
    ((integrable_const (2*(Real.log a)^2)).add ((log_inner_sq_integrable e).const_mul 2)) (by
      filter_upwards [inner_ne_zero_ae_sphere e] with u hu
      change (Real.log (g u))^2≤2*(Real.log a)^2+2*(Real.log |⟪(e:Space n),(u:Space n)⟫|)^2
      apply log_sq_coercive_bound (abs_pos.mpr hu) _ ha _ (hm u)
      · simpa only [norm_coe,mul_one] using abs_real_inner_le_norm (e:Space n) (u:Space n)
      · simpa only [real_inner_comm] using hb u)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) ((log_inner_sq_integrable e).const_mul 2),
    integral_const,integral_const_mul,probReal_univ,one_smul] at h
  change mean _ ≤ _+2*mean _ at h
  rw [mean_inner_independent (fun t => (Real.log |t|)^2) e (pole n)] at h
  linarith

lemma seminorm_log_integral_tendsto {n : ℕ} [NeZero n]
    {g : ℕ → Seminorm ℝ (Space n)} {f : Seminorm ℝ (Space n)} {r R : ℝ}
    (hr : 0<r) (hlo : ∀ i,∃ u : Sphere n,r≤g i u)
    (hhi : ∀ i (u : Sphere n),g i u≤R) (hf : f ≠ 0)
    (hc : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u))) :
    Tendsto (fun i => mean (fun u : Sphere n => Real.log (g i u))) atTop
      (𝓝 (mean (fun u : Sphere n => Real.log (f u)))) := by
  have hg (i : ℕ) : g i ≠ 0 := by
    intro h
    obtain ⟨u,hu⟩ := hlo i
    rw [h] at hu
    exact hr.not_ge hu
  apply tendsto_integral_of_sq_bound (C := 2*(|Real.log r|+|Real.log R|)^2+
    2*mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2))
  · have hp : 0 ≤ mean (fun u : Sphere n => (Real.log |⟪(pole n:Space n),(u:Space n)⟫|)^2) :=
      integral_nonneg (fun _ => sq_nonneg _)
    positivity
  · exact fun i => seminorm_log_integrable (hg i)
  · exact fun i => seminorm_log_sq_integrable (hg i)
  · exact fun i => seminorm_log_sq_bound hr (hlo i) (hhi i)
  · exact seminorm_log_integrable hf
  · filter_upwards [seminorm_pos_ae_sphere hf] with u hu
    exact (Real.continuousAt_log hu.ne').tendsto.comp (hc u)

end PettyProjection.Spherical
end

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma seminorm_lipschitz_of_sphere_bound {n : ℕ} (g : Seminorm ℝ (Space n))
    {R : ℝ≥0} (hR : ∀ u : Sphere n,g u≤R) : LipschitzWith R g := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |g x-g y|≤(R:ℝ)*dist x y
  exact (abs_sub_map_le_sub g x y).trans (by
    simpa only [dist_eq_norm] using seminorm_le_max_norm g hR (x-y))

def radialExtension {n : ℕ} (f : Sphere n → ℝ) (x : Space n) : ℝ :=
  if hx : x=0 then 0 else ‖x‖*f ⟨‖x‖⁻¹ • x,by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)⟩

lemma radialExtension_sphere {n : ℕ} (f : Sphere n → ℝ) (u : Sphere n) :
    radialExtension f u=f u := by
  have hu0 : (u:Space n)≠0 := by intro h; have := norm_coe u; simp [h] at this
  simp only [radialExtension,dite_eq_right hu0,norm_coe,inv_one,one_smul,one_mul]

lemma radialExtension_seminorm {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    radialExtension (fun u : Sphere n => g u) x=g x := by
  by_cases hx : x=0
  · simp [radialExtension,hx]
  · simp only [radialExtension,dite_eq_right hx,map_smul_eq_mul,Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg _))]
    rw [← mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_mul]

lemma radialExtension_tendsto {n : ℕ} {g : ℕ → Seminorm ℝ (Space n)}
    {f : Sphere n → ℝ} (h : ∀ u : Sphere n,Tendsto (fun i => g i u) atTop (𝓝 (f u)))
    (x : Space n) : Tendsto (fun i => g i x) atTop (𝓝 (radialExtension f x)) := by
  have he (i : ℕ) : g i x=radialExtension (fun u : Sphere n => g i u) x :=
    (radialExtension_seminorm (g i) x).symm
  simp_rw [he]
  unfold radialExtension
  split_ifs with hx
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds.mul (h _)

/-- Uniform sphere compactness of bounded seminorms, including all singular
limits. The limiting algebraic object is proved to be a seminorm. -/
theorem bounded_seminorm_subsequence {n : ℕ} (g : ℕ → Seminorm ℝ (Space n))
    {R : ℝ≥0} (hR : ∀ i (u : Sphere n),g i u≤R) :
    ∃ f : Seminorm ℝ (Space n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun i (u : Sphere n) => g (φ i) u) (fun u => f u) atTop ∧
      (∀ x,Tendsto (fun i => g (φ i) x) atTop (𝓝 (f x))) := by
  let F : ℕ → (BoundedContinuousFunction (Sphere n) ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨fun u => g i u,
      (seminorm_continuous n (g i)).comp continuous_subtype_val⟩
  have hL (i : ℕ) : LipschitzWith R (F i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (seminorm_lipschitz_of_sphere_bound (g i) (hR i)).dist_le_mul (x:Space n) (y:Space n)
  have hc : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0:ℝ) R) isCompact_Icc
    · intro f u hf
      obtain ⟨i,rfl⟩ := hf
      exact ⟨apply_nonneg (g i) (u:Space n),hR i u⟩
    · apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ R
      intro f
      obtain ⟨i,hi⟩ := f.property
      simpa only [hi] using hL i
  obtain ⟨f,_,φ,hφ,hconv⟩ := hc.tendsto_subseq (fun i => subset_closure (mem_range_self i))
  have hunif : TendstoUniformly (fun i => (F (φ i) : Sphere n → ℝ)) f atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  have hpoint := radialExtension_tendsto (g := fun i => g (φ i)) hunif.tendsto_at
  let q : Seminorm ℝ (Space n) := Seminorm.of (radialExtension f)
    (fun x y => le_of_tendsto_of_tendsto (hpoint (x+y)) ((hpoint x).add (hpoint y))
      (Eventually.of_forall (fun i => map_add_le_add (g (φ i)) x y)))
    (fun a x => tendsto_nhds_unique (hpoint (a • x)) (by
      simp_rw [map_smul_eq_mul]
      exact tendsto_const_nhds.mul (hpoint x)))
  refine ⟨q,φ,hφ,?_,hpoint⟩
  have he : (fun u : Sphere n => q u)=(f : Sphere n → ℝ) := by
    funext u; exact radialExtension_sphere f u
  rw [he]
  exact hunif

end PettyProjection.Spherical
end

noncomputable section
open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere seminorm_continuous)

/-- Closed unit set of the actual seminorm. It is allowed to be a cylinder. -/
def seminormUnit {n : ℕ} (g : Seminorm ℝ (Space n)) : Set (Space n) := {x | g x≤1}

lemma seminormUnit_zero {n : ℕ} (g : Seminorm ℝ (Space n)) : 0∈seminormUnit g := by
  simp [seminormUnit]

lemma seminormUnit_closed {n : ℕ} (g : Seminorm ℝ (Space n)) : IsClosed (seminormUnit g) :=
  isClosed_le (seminorm_continuous n g) continuous_const

lemma seminormUnit_convex {n : ℕ} (g : Seminorm ℝ (Space n)) : Convex ℝ (seminormUnit g) := by
  simpa only [seminormUnit,← g.closedBall_zero_eq] using g.convex_closedBall 0 1

lemma seminormUnit_balanced {n : ℕ} (g : Seminorm ℝ (Space n)) : Balanced ℝ (seminormUnit g) := by
  simpa only [seminormUnit,← g.closedBall_zero_eq] using g.balanced_closedBall_zero 1

lemma seminormUnit_nhds {n : ℕ} (g : Seminorm ℝ (Space n)) : seminormUnit g∈𝓝 (0:Space n) := by
  have ho : IsOpen {x : Space n | g x<1} := isOpen_lt (seminorm_continuous n g) continuous_const
  exact Filter.mem_of_superset (ho.mem_nhds (by simp)) (fun x hx => show g x≤1 from hx.le)

lemma gauge_seminormUnit {n : ℕ} (g : Seminorm ℝ (Space n)) (x : Space n) :
    gauge (seminormUnit g) x=g x := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hp : 0<g x+ε := add_pos_of_nonneg_of_pos (apply_nonneg g x) hε
    apply gauge_le_of_mem hp.le
    refine ⟨(g x+ε)⁻¹ • x,?_,smul_inv_smul₀ hp.ne' x⟩
    change g ((g x+ε)⁻¹ • x)≤1
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_le_iff₀ hp]
    linarith
  · unfold gauge
    apply le_csInf (absorbent_nhds_zero (seminormUnit_nhds g)).gauge_set_nonempty
    rintro r ⟨hr,y,hy,rfl⟩
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy

lemma seminormUnit_compact {n : ℕ} (g : Seminorm ℝ (Space n)) {c : ℝ}
    (hc : 0<c) (hbound : ∀ x,c*‖x‖≤g x) : IsCompact (seminormUnit g) := by
  apply (isCompact_closedBall (0:Space n) c⁻¹).of_isClosed_subset (seminormUnit_closed g)
  intro x hx
  rw [mem_closedBall,dist_zero_right,inv_eq_one_div,le_div_iff₀ hc]
  change g x≤1 at hx
  nlinarith [hbound x]

lemma seminorm_pos_uniform {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n))
    (hg : ∀ u : Sphere n,0<g u) : ∃ c : ℝ, 0<c ∧ ∀ x,c*‖x‖≤g x := by
  let : Nonempty (Sphere n) := ⟨Spherical.pole n⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set (Sphere n)).Nonempty)
    ((seminorm_continuous n g).comp continuous_subtype_val).continuousOn
  refine ⟨g u,hg u,fun x => ?_⟩
  by_cases hx : x=0
  · simp [hx]
  · let v : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,norm_ne_zero_iff.mpr hx]⟩
    have hh : g u≤g v := hu (mem_univ v)
    change g u≤g (‖x‖⁻¹ • x) at hh
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hh
    have hp : 0<‖x‖ := norm_pos_iff.mpr hx
    have hh' := mul_le_mul_of_nonneg_left hh hp.le
    rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul] at hh'
    simpa only [mul_comm] using hh'

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere)

lemma integrable_abs_inner {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) (y : Space n) :
    Integrable (fun x => |⟪x,y⟫|) μ := by
  apply (hμ.mul_const ‖y‖).mono' (by fun_prop)
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm x y)

/-- The actual cosine-transform norm furnished by a spanning measure. -/
def cosineSeminorm {n : ℕ} (μ : Measure (Space n))
    (hμ : Integrable (fun x : Space n => ‖x‖) μ) : Seminorm ℝ (Space n) :=
  Seminorm.of (fun y => ∫ x,|⟪x,y⟫| ∂μ)
    (fun y z => by
      rw [← integral_add (integrable_abs_inner hμ y) (integrable_abs_inner hμ z)]
      apply integral_mono (integrable_abs_inner hμ (y+z))
        ((integrable_abs_inner hμ y).add (integrable_abs_inner hμ z))
      intro x
      change |⟪x,y+z⟫|≤ |⟪x,y⟫|+|⟪x,z⟫|
      rw [inner_add_right]
      exact abs_add_le _ _)
    (fun a y => by
      simp only [inner_smul_right,abs_mul,Real.norm_eq_abs,integral_const_mul])

lemma support_integrable {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    Integrable (support K) μ := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  apply (hμ.const_mul R).mono' (support_continuous hK).aestronglyMeasurable
  refine Eventually.of_forall (fun x => ?_)
  obtain ⟨y,hy,he⟩ := support_attained hK hne x
  rw [Real.norm_eq_abs,he]
  exact (abs_real_inner_le_norm x y).trans (by nlinarith [norm_nonneg x,hbound y hy])

lemma abs_inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hsym : ∀ y∈K,-y∈K) {y : Space n} (hy : y∈K) (x : Space n) :
    |⟪x,y⟫|≤ support K x := by
  rw [abs_le]
  constructor
  · have hh := inner_le_support hK (hsym y hy) x
    rw [inner_neg_right] at hh
    linarith
  · exact inner_le_support hK hy x

lemma cosine_le_functional {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K : Set (Space n)} (hK : IsCompact K) (hsym : ∀ y∈K,-y∈K)
    {y : Space n} (hy : y∈K) : cosineSeminorm μ hμ y≤ supportFunctional μ K := by
  exact integral_mono (integrable_abs_inner hμ y) (support_integrable hμ hK ⟨y,hy⟩)
    (abs_inner_le_support hK hsym hy)

lemma functional_smul {n : ℕ} {μ : Measure (Space n)}
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) {a : ℝ} (ha : 0≤a) :
    supportFunctional μ (a • K)=a*supportFunctional μ K := by
  unfold supportFunctional
  simp_rw [support_smul_set hK hne ha]
  exact integral_const_mul _ _

lemma functional_add {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    {K L : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hLn : L.Nonempty) :
    supportFunctional μ (K+L)=supportFunctional μ K+supportFunctional μ L := by
  unfold supportFunctional
  simp_rw [support_minkowski hK hKn hL hLn]
  exact integral_add (support_integrable hμ hK hKn) (support_integrable hμ hL hLn)

lemma functional_nonneg {n : ℕ} {μ : Measure (Space n)}
    {K : Set (Space n)} (hK : IsCompact K) (hK0 : 0∈K) : 0≤ supportFunctional μ K :=
  integral_nonneg (fun x => support_nonneg hK hK0 x)

end PettyProjection
end

end OAI
