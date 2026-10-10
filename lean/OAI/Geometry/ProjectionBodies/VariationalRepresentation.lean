import OAI.Geometry.ProjectionBodies.VariationalMinimizers

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere sigma mean objective objectiveIntegrand)
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

/-- Actual Euler equation for the normalized variational optimizer. The test
is only continuous, even and degree-one homogeneous, not assumed convex. -/
theorem normalized_representation {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      objective b g.toSeminorm≤objective b q.toSeminorm)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ a : ℝ,0<a → ∀ x,φ (a • x)=a*φ x) :
    (∫ x,φ x ∂μ)*(if b then 1 else objective false g.toSeminorm)=
      mean (fun u : Sphere n => (if b then 1 else g u)*φ (∇ (fun x => g x) (u:Space n))) := by
  let s : C(Sphere n,ℝ) := ⟨fun u => support g.body u,(support_continuous g.compact).comp continuous_subtype_val⟩
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  have hs : ∀ u,0<s u := support_pos_of_nhds g.compact g.top_nhds
  have hw : wulff s=g.body := wulff_support g.compact g.convex g.nonempty
  have hge : gauge (wulff s)=(fun x => g x) := by ext x; rw [hw,g.top_gauge]
  let I := ∫ x,φ x ∂μ
  let F : ℝ → ℝ := fun t => mean (fun u : Sphere n => objectiveIntegrand b (gauge (wulff ⇑(s+t • φs)) (u:Space n)))
  let D := mean (fun u : Sphere n => (if b then 1 else g u)*φ (∇ (fun x => g x) (u:Space n)))
  let H : ℝ → ℝ := fun t => if b then Real.log (1+t*I)+F t else (1+t*I)*F t
  have hF0 : F 0=objective b g.toSeminorm := by
    simp only [F,zero_smul,add_zero,hge,objective]
  have hFder : HasDerivAt F (-D) 0 := by
    have h := wulff_objective_derivative b s hs φ hφ hh
    rw [hge] at h
    exact h
  have hlin : HasDerivAt (fun t : ℝ => 1+t*I) I 0 := by
    simpa only [one_mul,id_eq] using (((hasDerivAt_id (0:ℝ)).mul_const I).const_add 1)
  have hH0 : H 0=objective b g.toSeminorm := by
    dsimp only [H]; rw [zero_mul,add_zero,Real.log_one,zero_add,one_mul]; split <;> exact hF0
  have hHder : HasDerivAt H (I*(if b then 1 else objective false g.toSeminorm)-D) 0 := by
    cases b
    · have hd := hlin.mul hFder
      simpa only [Pi.mul_def,H,Bool.false_eq_true,ite_false,zero_mul,add_zero,one_mul,hF0,mul_neg,one_mul,sub_eq_add_neg] using hd
    · have hd := (hlin.log (by norm_num)).add hFder
      simpa only [Pi.add_def,H,ite_true,zero_mul,add_zero,div_one,mul_one,sub_eq_add_neg] using hd
  have hHmin : IsLocalMin H 0 := by
    have hpos : ∀ᶠ t in 𝓝 (0:ℝ),0<1+t*I := by
      have hc : Continuous (fun t : ℝ => 1+t*I) := by fun_prop
      have hh := hc.continuousAt.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1+0*I))
      exact hh
    filter_upwards [positive_constraints_nhds s φs hs,hpos] with t ht htp
    rw [hH0]
    have hsym : ∀ u : Sphere n,(s+t • φs) ⟨-(u:Space n),by simp⟩=(s+t • φs) u := by
      intro u
      change support g.body (-(u:Space n))+t*φ (-(u:Space n))=support g.body u+t*φ u
      rw [support_even g.compact g.nonempty (fun _ h => g.neg_mem h),heven]
    let f := ofFullBody (wulff_compact (s+t • φs) ht) (wulff_convex _) (wulff_balanced _ hsym) (wulff_nhds (s+t • φs) ht)
    have hfb : f.body=wulff ⇑(s+t • φs) := body_ofFullBody _ _ _ _
    have hbound : supportFunctional μ f.body≤1+t*I := by
      rw [hfb]
      have hb := functional_wulff_bound hμ g.compact g.nonempty φ hφ hh t ht
      rw [hgn] at hb
      exact hb
    have hlo := minimizer_scaled_lower hμ (show (⊤ : Submodule ℝ (Space n))≠⊥ from top_ne_bot)
      (fun x _ hx => hq x hx) b hmin f htp hbound
    have hscale := Spherical.objective_scale b (g := f.toSeminorm)
      (f := (f.scale (1+t*I) htp).toSeminorm) (f.ne_zero top_ne_bot) htp (fun _ => rfl)
    rw [hscale] at hlo
    have hfobj : objective b f.toSeminorm=F t := by
      unfold objective
      congr 1
      funext u
      rw [← f.top_gauge,hfb]
    rw [hfobj] at hlo
    exact hlo
  have hz := hHmin.hasDerivAt_eq_zero hHder
  exact sub_eq_zero.mp hz

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean sigma)

lemma normalizedVolume_pos {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < normalizedVolume K :=
  div_pos (volumeRoot_pos hK hi) (Real.rpow_pos_of_pos (kappa_pos n) _)

lemma normalizedVolume_pow {n : ℕ} [NeZero n] (K : Set (Space n)) :
    normalizedVolume K^n=volume.real K/kappa n := by
  rw [normalizedVolume_formula]
  exact Real.rpow_inv_natCast_pow (div_nonneg measureReal_nonneg (kappa_pos n).le) (NeZero.ne n)

lemma normalizedVolume_smul {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 ≤ a) (K : Set (Space n)) :
    normalizedVolume (a • K)=a*normalizedVolume K := by
  rw [normalizedVolume,volumeRoot_smul (NeZero.pos n) ha,normalizedVolume]
  ring

namespace RelativeGauge
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma top_pos (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (u : Sphere n) : 0 < g u :=
  g.pos (Submodule.mem_top) (by intro h;simpa [h] using norm_coe u)

omit [NeZero n] in
lemma top_interior (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : (interior g.body).Nonempty :=
  ⟨0,mem_interior_iff_mem_nhds.mpr g.top_nhds⟩

def volumeNormalize (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    RelativeGauge (⊤ : Submodule ℝ (Space n)) :=
  g.scale (normalizedVolume g.body) (normalizedVolume_pos g.compact g.top_interior)

lemma volumeNormalize_body_volume (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    volume.real g.volumeNormalize.body=kappa n := by
  have ha := normalizedVolume_pos g.compact g.top_interior
  rw [volumeNormalize,g.body_scale,volumeReal_smul_nonneg (inv_nonneg.mpr ha.le),
    finrank_euclideanSpace_fin,inv_pow,normalizedVolume_pow]
  field_simp [(volumeReal_pos_of_body g.compact g.top_interior).ne',(kappa_pos n).ne']

lemma volumeNormalize_moment (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) :
    mean (fun u : Sphere n => (g.volumeNormalize u)⁻¹^n)=1 := by
  have hh := gauge_volume g.volumeNormalize.convex g.volumeNormalize.top_nhds
    (fun u => by rw [g.volumeNormalize.top_gauge];exact g.volumeNormalize.top_pos u)
  simp_rw [g.volumeNormalize.top_gauge] at hh
  rw [g.volumeNormalize_body_volume] at hh
  exact (mul_left_cancel₀ (kappa_pos n).ne' (by simpa only [mul_one] using hh.symm))

omit [NeZero n] in
lemma full_body_of_sphere_one (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    (hg : ∀ u : Sphere n,g u=1) : g.body=unitBall n := by
  have he (x : Space n) : g x=‖x‖ := by
    by_cases hx : x=0
    · simp [hx]
    let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
    have h := hg u
    change g.toSeminorm (‖x‖⁻¹ • x)=1 at h
    rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at h
    have hn := norm_ne_zero_iff.mpr hx
    field_simp at h
    exact h
  ext x
  rw [g.top_body]
  change g x≤1 ↔ x∈closedBall 0 1
  rw [he,mem_closedBall,dist_zero_right]

def fullOfRange {A : Space n →L[ℝ] Space n} (hA : LinearMap.range A.toLinearMap=⊤)
    (g : RelativeGauge (LinearMap.range A.toLinearMap)) : RelativeGauge (⊤ : Submodule ℝ (Space n)) where
  toSeminorm := g.toSeminorm
  projection x := by rw [Submodule.starProjection_top];rfl
  lower := by simpa only [hA] using g.lower

omit [NeZero n] in
lemma fullOfRange_body {A : Space n →L[ℝ] Space n} (hA : LinearMap.range A.toLinearMap=⊤)
    (g : RelativeGauge (LinearMap.range A.toLinearMap)) : (fullOfRange hA g).body=g.body := by
  simp only [body,fullOfRange,hA]

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment)

def regime (n : ℕ) : Bool := decide (n=4)
lemma exponent_pos (n : ℕ) : 0 < Scalar.exponent n := by unfold Scalar.exponent;split_ifs <;> norm_num

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma scale_field_ae (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) {a : ℝ} (ha : 0 < a)
    {k : ℕ} (hk : 0 < k) :
    gaugeField (g.scale a ha).toSeminorm k =ᵐ[sigma n] (fun u => a^k • gaugeField g.toSeminorm k u) := by
  filter_upwards [Spherical.seminorm_ae_differentiable_sphere g.toSeminorm] with u hu
  have hgrad : ∇ (fun x => g.scale a ha x) (u:Space n)=a • ∇ (fun x => g x) (u:Space n) := by
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    rw [toDual_gradient,map_smul,toDual_gradient]
    exact fderiv_const_mul hu a
  change (a*g u)^(k-1) • ∇ (fun x => g.scale a ha x) (u:Space n)=_
  rw [hgrad,mul_pow,smul_smul]
  change (a^(k-1)*g u^(k-1)*a) • _=a^k • (g u^(k-1) • _)
  rw [smul_smul]
  congr 1
  have hp : a^k=a^(k-1)*a := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
  rw [hp]
  ring

omit [NeZero n] in
lemma scale_moment (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    gaugeMoment (g.scale a ha).toSeminorm k=a^k*gaugeMoment g.toSeminorm k := by
  change mean (fun u : Sphere n => (a*g u)^k)=_
  simp only [mul_pow,gaugeMoment,mean,integral_const_mul]

lemma minimizer_field_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ a : ℝ,0 < a → ∀ x,φ (a • x)=a*φ x) :
    (∫ x,φ x ∂μ)*gaugeMoment g.toSeminorm (Scalar.exponent n-1)=
      mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u)) := by
  have hv := normalized_representation hμ hq (regime n) g hgn hmin φ hφ heven hh
  have he : mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u))=
      mean (fun u : Sphere n => (if regime n then 1 else g u)*φ (∇ (fun x => g x) (u:Space n))) := by
    congr 1
    funext u
    by_cases hn : n=4
    · simp [gaugeField,Scalar.exponent,regime,hn]
    · simp only [gaugeField,Scalar.exponent,ite_eq_right hn,Nat.reduceSub,pow_one,
        regime,decide_eq_false hn,Bool.false_eq_true,ite_false]
      exact hh _ (g.top_pos u) _
  rw [he]
  convert hv using 1
  congr 1
  by_cases hn : n=4
  · simp [gaugeMoment,Scalar.exponent,regime,hn,Spherical.mean_const]
  · simp [gaugeMoment,Scalar.exponent,regime,hn,Spherical.objective,Spherical.objectiveIntegrand]

lemma scaled_field_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    {a : ℝ} (ha : 0 < a)
    (φ : Space n → ℝ) (hφ : Continuous φ) (heven : ∀ x,φ (-x)=φ x)
    (hh : ∀ r : ℝ,0 < r → ∀ x,φ (r • x)=r*φ x) :
    (∫ x,φ x ∂μ)*gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1)=
      supportFunctional μ (g.scale a ha).body*
        mean (fun u : Sphere n => φ (gaugeField (g.scale a ha).toSeminorm (Scalar.exponent n) u)) := by
  have he : mean (fun u : Sphere n => φ (gaugeField (g.scale a ha).toSeminorm (Scalar.exponent n) u))=
      a^(Scalar.exponent n)*mean (fun u : Sphere n => φ (gaugeField g.toSeminorm (Scalar.exponent n) u)) := by
    simp only [mean]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [g.scale_field_ae ha (exponent_pos n)] with u hu
    rw [hu,hh _ (pow_pos ha _)]
  rw [g.scale_moment ha,g.functional_scale,hgn,mul_one,he]
  have hr := minimizer_field_representation hμ hq g hgn hmin φ hφ heven hh
  rw [← hr]
  have hk : a^(Scalar.exponent n)=a^(Scalar.exponent n-1)*a := by
    rw [← pow_succ];congr 1;have := exponent_pos n;omega
  rw [hk]
  field_simp

end RelativeGauge
end PettyProjection
end

end OAI
