import OAI.Geometry.ProjectionBodies.PositionMatrices

namespace OAI

universe uX

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeField gaugeMoment absolutePair)

/-- The genuine unpolarized cosine pairing of two (not necessarily even) measures. -/
def measurePair {n : ℕ} (μ ν : Measure (Space n)) : ℝ :=
  ∫ x,∫ y,|⟪x,y⟫| ∂ν ∂μ

def Represents {n : ℕ} (μ : Measure (Space n)) (g : Seminorm ℝ (Space n)) (k : ℕ) (s : ℝ) : Prop :=
  ∀ (φ : Space n → ℝ),Continuous φ → (∀ x,φ (-x)=φ x) →
    (∀ r : ℝ,0 < r → ∀ x,φ (r • x)=r*φ x) →
      (∫ x,φ x ∂μ)=s*mean (fun u : Sphere n => φ (gaugeField g k u))

lemma represents_pair {n : ℕ} [NeZero n] {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (f g : Seminorm ℝ (Space n)) {k : ℕ} (hk : 0 < k) {s t : ℝ}
    (hf : Represents μ f k s) (hg : Represents ν g k t) :
    measurePair μ ν=s*t*absolutePair (gaugeField f k) (gaugeField g k) := by
  have hcos : measurePair μ ν=∫ x,cosineSeminorm ν hν x ∂μ := by
    unfold measurePair
    apply integral_congr_ae
    filter_upwards [] with x
    change (∫ y,|⟪x,y⟫| ∂ν)=∫ y,|⟪y,x⟫| ∂ν
    simp only [real_inner_comm x]
  rw [hcos,hf _ (Spherical.seminorm_continuous n _) (fun x => map_neg_eq_map _ x)
    (fun r hr x => by rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le])]
  have he (u : Sphere n) : cosineSeminorm ν hν (gaugeField f k u)=
      t*mean (fun v : Sphere n => |⟪gaugeField f k u,gaugeField g k v⟫|) := by
    have hh := hg (fun x => |⟪gaugeField f k u,x⟫|) (by fun_prop)
      (fun x => by simp) (fun r hr x => by simp only [inner_smul_right,abs_mul,abs_of_pos hr])
    change (∫ x,|⟪x,gaugeField f k u⟫| ∂ν)=_
    simpa only [real_inner_comm (gaugeField f k u)] using hh
  simp_rw [he]
  rw [mean,integral_const_mul,mul_assoc]
  congr 1
  congr 1
  exact (integral_prod _ (Spherical.gaugeField_absolute_integrable f g hk)).symm

namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

lemma scaled_represents
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective (regime n) g.toSeminorm≤Spherical.objective (regime n) q.toSeminorm)
    {a : ℝ} (ha : 0 < a) :
    Represents μ (g.scale a ha).toSeminorm (Scalar.exponent n)
      (supportFunctional μ (g.scale a ha).body/gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1)) := by
  intro φ hφ he hh
  have ht : 0 < gaugeMoment (g.scale a ha).toSeminorm (Scalar.exponent n-1) :=
    Position.mean_power_pos _ ((g.scale a ha).ne_zero top_ne_bot) _
  have h := scaled_field_representation hμ hq g hgn hmin ha φ hφ he hh
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff ht.ne').mpr h

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere norm_coe)

lemma compact_inward {X : Type uX} [TopologicalSpace X] [CompactSpace X]
    {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x,0≤a x) (hab : ∀ x,a x=0 → b x<0) :
    ∃ ε : ℝ,0<ε ∧ ∀ x,0<a x-ε*b x := by
  let K : Set X := {x | 0≤b x}
  have hK : IsCompact K := (isClosed_le continuous_const hb).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne ha.continuousOn
    have hax : 0<a x := lt_of_le_of_ne (ha0 x) (fun h => (hab x h.symm).not_ge hx)
    obtain ⟨M,hM,hbound⟩ := (isCompact_univ.image hb).isBounded.exists_pos_norm_le
    let ε := a x/(2*M)
    have hε : 0<ε := div_pos hax (by positivity)
    refine ⟨ε,hε,fun y => ?_⟩
    by_cases hy : y∈K
    · have hmy : a x≤a y := hmin hy
      have hbM : b y≤M := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound (b y) ⟨y,mem_univ _,rfl⟩)
      have hh : ε*M=a x/2 := by dsimp [ε]; field_simp
      have hle := mul_le_mul_of_nonneg_left hbM hε.le
      rw [hh] at hle
      linarith
    · have hby : b y<0 := lt_of_not_ge hy
      have hneg := mul_neg_of_pos_of_neg hε hby
      linarith [ha0 y]
  · refine ⟨1,zero_lt_one,fun y => ?_⟩
    have hby : b y<0 := by
      by_contra h
      exact hne ⟨y,le_of_not_gt h⟩
    linarith [ha0 y]

lemma inward_perturbation {n : ℕ} [NeZero n] {A F : Mat n} (hA : A∈domain n)
    (hF : Symmetric F) (htr : tr F=0)
    (hker : ∀ e : Sphere n,op A e=0 → quad F e<0) :
    ∃ ε : ℝ,0<ε ∧ A-ε • F∈domain n ∧ ∀ x : Space n,x≠0 → 0<quad (A-ε • F) x := by
  have hca : Continuous (fun u : Sphere n => quad A u) :=
    by simp_rw [quad_eq]; fun_prop
  have hcf : Continuous (fun u : Sphere n => quad F u) :=
    by simp_rw [quad_eq]; fun_prop
  obtain ⟨ε,hε,hp⟩ := compact_inward hca hcf (fun u => hA.1.2 u)
    (fun u hu => hker u (op_kernel_of_quad_zero hA.1 hu))
  have hq : ∀ x : Space n,x≠0 → 0<quad (A-ε • F) x := by
    intro x hx
    let u : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
    have hh := hp u
    rw [← quad_smul,← quad_sub] at hh
    have he : quad (A-ε • F) u=‖x‖⁻¹^2*quad (A-ε • F) x := by
      simp only [quad,u,map_smul,inner_smul_left,inner_smul_right,conj_trivial]
      ring
    rw [he] at hh
    exact (mul_pos_iff.mp hh).resolve_right (fun h => (sq_nonneg ‖x‖⁻¹).not_gt h.1) |>.2
  refine ⟨ε,hε,⟨⟨?_,?_⟩,?_⟩,hq⟩
  · intro i j
    change A (i,j)-ε*F (i,j)=A (j,i)-ε*F (j,i)
    rw [hA.1.1 i j,hF i j]
  · intro x
    by_cases hx : x=0
    · simp [hx,quad]
    · exact (hq x hx).le
  · change (∑ i,(A (i,i)-ε*F (i,i)))=1
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    change tr A-ε*tr F=1
    rw [hA.2,htr,mul_zero,sub_zero]

/-- The topological mechanism. The field is genuine and continuous;
its negativity on every null direction forces an interior zero. -/
theorem traceOne_field_zero {n : ℕ} [NeZero n] (F : {A : Mat n // A∈domain n} → Mat n)
    (hFc : Continuous F) (hFs : ∀ A,Symmetric (F A)) (hFt : ∀ A,tr (F A)=0)
    (hFk : ∀ A (e : Sphere n),op A.val e=0 → quad (F A) e<0) :
    ∃ A : {A : Mat n // A∈domain n},F A=0 ∧ Function.Injective (op A.val) := by
  let p := FixedPoint.nearest (domain n) domain_nonempty domain_compact.isComplete domain_convex
  have hp (x : Mat n) : p x∈domain n := FixedPoint.nearest_mem _ _ _ _ x
  have hpc : Continuous p := (FixedPoint.nearest_lipschitz _ _ _ _).continuous
  let f : Mat n → Mat n := fun x => p (x-F ⟨p x,hp x⟩)
  have hfc : Continuous f := hpc.comp (continuous_id.sub (hFc.comp (hpc.subtype_mk hp)))
  obtain ⟨A,hA,hfix⟩ := FixedPoint.fixedPoint_compact_convex domain_nonempty domain_compact domain_convex
    hfc.continuousOn (fun x _ => hp _)
  let a : {A : Mat n // A∈domain n} := ⟨A,hA⟩
  have hpa : p A=A := FixedPoint.nearest_eq_of_mem _ _ _ _ hA
  have hfix' : p (A-F a)=A := by simpa only [f,hpa] using hfix
  have hi := FixedPoint.nearest_inner (domain n) domain_nonempty domain_compact.isComplete domain_convex (A-F a)
  change ∀ z∈domain n,⟪A-F a-p (A-F a),z-p (A-F a)⟫≤0 at hi
  rw [hfix'] at hi
  obtain ⟨ε,hε,hB,_⟩ := inward_perturbation hA (hFs a) (hFt a) (hFk a)
  have hh := hi (A-ε • F a) hB
  have hf0 : F a=0 := by
    simp only [sub_sub_cancel_left,inner_neg_left,inner_neg_right,inner_smul_right,real_inner_self_eq_norm_sq] at hh
    have hs : ‖F a‖^2≤0 := nonpos_of_mul_nonpos_left (by nlinarith only [hh]) hε
    have hn : ‖F a‖=0 := by nlinarith [norm_nonneg (F a)]
    exact norm_eq_zero.mp hn
  refine ⟨a,hf0,?_⟩
  apply (op A).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change op A x=0 at hx
  by_contra hx0
  let e : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]⟩
  have he : op A e=0 := by change op A (‖x‖⁻¹ • x)=0; rw [map_smul,hx,smul_zero]
  have hh := hFk a e he
  rw [hf0] at hh
  simp only [quad_eq] at hh
  simp at hh
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical (Sphere mean seminorm_continuous)
open RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

abbrev Domain (n : ℕ) := {A : Mat n // A∈domain n}
instance domain_compactSpace : CompactSpace (Domain n) := isCompact_iff_compactSpace.mp domain_compact

def domainMap (A : Domain n) : NonzeroMap n := ⟨op A.val,domain_range_ne_bot A.property⟩
omit [NeZero n] in
lemma domainMap_continuous : Continuous (domainMap : Domain n → NonzeroMap n) :=
  (op_continuous.comp continuous_subtype_val).subtype_mk _

lemma optimizer_kernel (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (A : Domain n)
    (e : Space n) (he : op A.val e=0) : optimizer hμ hq b (domainMap A) e=0 := by
  let V := LinearMap.range (op A.val).toLinearMap
  have hp : V.starProjection e=0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (V.zero_mem)
    rintro y ⟨z,rfl⟩
    simp only [sub_zero]
    have hs := symmetric_op A.property.1.1 e z
    change ⟪op A.val e,z⟫=⟪e,op A.val z⟫ at hs
    rw [he,inner_zero_left] at hs
    exact hs.symm
  have hh := (optimizer hμ hq b (domainMap A)).projection e
  change (optimizer hμ hq b (domainMap A)) (V.starProjection e)=_ at hh
  rw [hp] at hh
  exact hh.symm.trans (map_zero _)

lemma optimizer_joint_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) :
    Continuous (fun p : Domain n × Sphere n => optimizer hμ hq b (domainMap p.1) p.2) := by
  exact ((optimizerSphere_continuous hμ hq b).comp domainMap_continuous).fst'.eval continuous_snd

def positionField (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (k : ℕ) (A : Domain n) : Mat n :=
  momentField (optimizer hμ hq b (domainMap A)).toSeminorm k

lemma positionField_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) (k : ℕ) :
    Continuous (positionField hμ hq b k) := by
  have hg := optimizer_joint_continuous hμ hq b
  have hm : Continuous (fun A : Domain n => mean (fun u : Sphere n => optimizer hμ hq b (domainMap A) u^k)) := by
    simpa only [Measure.restrict_univ,mean] using
      (continuous_parametric_integral_of_continuous (μ := Spherical.sigma n) (hg.pow k) isCompact_univ)
  have hij (i j : Fin n) : Continuous (fun A : Domain n => mean (fun u : Sphere n =>
      optimizer hμ hq b (domainMap A) u^k*(u:Space n) i*(u:Space n) j)) := by
    have hc : Continuous (fun p : Domain n × Sphere n =>
        optimizer hμ hq b (domainMap p.1) p.2^k*(p.2:Space n) i*(p.2:Space n) j) :=
      (hg.pow k).mul (by fun_prop) |>.mul (by fun_prop)
    simpa only [Measure.restrict_univ,mean] using
      (continuous_parametric_integral_of_continuous (μ := Spherical.sigma n) hc isCompact_univ)
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ij
  exact ((hij ij.1 ij.2).div hm (fun A =>
    (mean_power_pos _ ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property) k).ne')).sub continuous_const

/-- A genuine nonsingular affine position for the variational optimizer. The
trace-one representative is used here; determinant normalization is a scalar
change and is performed in the global assembly. -/
theorem exists_optimizer_position (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x) (b : Bool) {k : ℕ} (hk : 0<k) :
    ∃ A : Domain n,Function.Injective (op A.val) ∧
      momentField (optimizer hμ hq b (domainMap A)).toSeminorm k=0 := by
  obtain ⟨A,hA,hinj⟩ := traceOne_field_zero (positionField hμ hq b k)
    (positionField_continuous hμ hq b k)
    (fun A => field_symmetric _ k)
    (fun A => field_trace _ ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property) k)
    (fun A e he => field_kernel ((optimizer hμ hq b (domainMap A)).ne_zero (domainMap A).property)
      hk e (optimizer_kernel hμ hq b A e he))
  exact ⟨A,hinj,hA⟩
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma volumeReal_linearEquiv (T : Space n ≃L[ℝ] Space n) (K : Set (Space n)) :
    volume.real (T '' K)=|LinearMap.det T.toLinearMap| * volume.real K := by
  unfold Measure.real
  rw [Measure.addHaar_image_continuousLinearEquiv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]

lemma linearEquiv_body (T : Space n ≃L[ℝ] Space n) {K : Set (Space n)} (hK : IsConvexBody K) :
    IsConvexBody (T '' K) := by
  refine ⟨hK.1.image T.continuous,hK.2.1.linear_image T.toLinearMap,?_⟩
  change (interior (T.toHomeomorph '' K)).Nonempty
  rw [← T.toHomeomorph.image_interior]
  exact hK.2.2.image T

lemma linearEquiv_det_ne_zero (T : Space n ≃L[ℝ] Space n) : LinearMap.det T.toLinearMap≠0 :=
  T.toLinearEquiv.isUnit_det'.ne_zero

def volumeFactor (T : Space n ≃L[ℝ] Space n) : ℝ := |LinearMap.det T.toLinearMap|^((n:ℝ)⁻¹)
lemma volumeFactor_pos (T : Space n ≃L[ℝ] Space n) : 0 < volumeFactor T :=
  Real.rpow_pos_of_pos (abs_pos.mpr (linearEquiv_det_ne_zero T)) _

lemma normalizedVolume_linearEquiv (T : Space n ≃L[ℝ] Space n) (K : Set (Space n)) :
    normalizedVolume (T '' K)=volumeFactor T*normalizedVolume K := by
  rw [normalizedVolume,volumeRoot,volumeReal_linearEquiv,
    Real.mul_rpow (abs_nonneg _) measureReal_nonneg]
  unfold volumeFactor normalizedVolume volumeRoot
  ring

lemma volumeFactor_symm (T : Space n ≃L[ℝ] Space n) : volumeFactor T.symm=(volumeFactor T)⁻¹ := by
  unfold volumeFactor
  rw [show T.symm.toLinearMap=(T.toLinearEquiv.symm : Space n →ₗ[ℝ] Space n) from rfl,
    LinearEquiv.det_coe_symm,abs_inv,Real.inv_rpow (abs_nonneg _)]

lemma symmetric_equiv_symm (T : Space n ≃L[ℝ] Space n) (hT : T.toLinearMap.IsSymmetric) :
    T.symm.toLinearMap.IsSymmetric := by
  intro x y
  change ⟪T.symm x,y⟫=⟪x,T.symm y⟫
  have hh := hT (T.symm x) (T.symm y)
  change ⟪T (T.symm x),T.symm y⟫=⟪T.symm x,T (T.symm y)⟫ at hh
  simpa only [T.apply_symm_apply] using hh.symm

lemma functional_map_symmetric {μ : Measure (Space n)} (T : Space n ≃L[ℝ] Space n)
    (hT : T.toLinearMap.IsSymmetric) {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    supportFunctional (μ.map T) K=supportFunctional μ (T '' K) := by
  change supportFunctional (μ.map T.toContinuousLinearMap) K=_
  rw [functional_map T.toContinuousLinearMap hK]
  unfold supportFunctional
  apply integral_congr_ae
  filter_upwards [] with x
  change support K (T.toContinuousLinearMap x)=support (T.toContinuousLinearMap '' K) x
  rw [support_linear_image hK hne T.toContinuousLinearMap,hT.clm_adjoint_eq]

lemma measurePair_cosine {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν) :
    measurePair μ ν=∫ x,cosineSeminorm ν hν x ∂μ := by
  unfold measurePair
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y,|⟪x,y⟫| ∂ν)=∫ y,|⟪y,x⟫| ∂ν
  simp only [real_inner_comm x]

lemma measurePair_map_symmetric {μ ν : Measure (Space n)}
    (hν : Integrable (fun x : Space n => ‖x‖) ν)
    (T : Space n ≃L[ℝ] Space n) (hT : T.toLinearMap.IsSymmetric) :
    measurePair (μ.map T) (ν.map T.symm)=measurePair μ ν := by
  change measurePair (μ.map T.toContinuousLinearMap) (ν.map T.symm.toContinuousLinearMap)=_
  rw [measurePair_cosine (norm_integrable_map hν T.symm.toContinuousLinearMap),
    integral_map T.toContinuousLinearMap.continuous.measurable.aemeasurable (Spherical.seminorm_continuous n _).aestronglyMeasurable,
    measurePair_cosine hν]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cosine_map ν hν T.symm.toContinuousLinearMap,(symmetric_equiv_symm T hT).clm_adjoint_eq]
  simp

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection.Position
open Spherical
variable {n : ℕ} [NeZero n]

lemma mean_inner_sq (x : Space n) : (n:ℝ)*mean (fun u : Sphere n => ⟪x,(u:Space n)⟫^2)=‖x‖^2 := by
  by_cases hx : x=0
  · simp [hx,mean]
  let e : Sphere n := ⟨‖x‖⁻¹ • x,by rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he := sphere_kernel_moment (0 : Seminorm ℝ (Space n)) 0 e (by simp)
  simp only [Nat.cast_zero,add_zero,pow_zero,one_mul,mean_const] at he
  have hh : mean (fun u : Sphere n => ⟪(e:Space n),(u:Space n)⟫^2)=
      ‖x‖⁻¹^2*mean (fun u : Sphere n => ⟪x,(u:Space n)⟫^2) := by
    simp only [e,inner_smul_left,conj_trivial,mul_pow,mean,integral_const_mul]
  rw [hh] at he
  have hn := norm_ne_zero_iff.mpr hx
  field_simp at he
  nlinarith [sq_pos_of_ne_zero hn]

omit [NeZero n] in
lemma symmetric_eq_zero_of_quad {A : Mat n} (hA : Symmetric A) (hq : ∀ x,quad A x=0) : A=0 := by
  have hd (i : Fin n) : A (i,i)=0 := by rw [← quad_basis,hq]
  apply WithLp.ofLp_injective
  funext ij
  have hh := hq (EuclideanSpace.single ij.1 1+EuclideanSpace.single ij.2 1)
  have he := quad_basis_add A ij.1 ij.2 1 1
  simp only [one_smul,one_pow,one_mul,hd,hA ij.2 ij.1] at he
  change A ij=0
  linarith

lemma constantMomentField_zero : momentField (0 : Seminorm ℝ (Space n)) 0=0 := by
  apply symmetric_eq_zero_of_quad (field_symmetric _ _) (fun x => ?_)
  rw [field_quad]
  simp only [pow_zero,one_mul,mean_const,div_one]
  have hm := mean_inner_sq x
  have hn : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [sub_eq_zero,eq_div_iff hn]
  linarith

lemma coordinateProduct_mean (i j : Fin n) : mean (coordinateProduct n i j)=(if i=j then 1 else 0)/(n:ℝ) := by
  have hh := congrArg (fun A : Mat n => A (i,j)) (constantMomentField_zero (n := n))
  change mean (fun u : Sphere n => (0 : Seminorm ℝ (Space n)) u^0*(u:Space n) i*(u:Space n) j)/
    mean (fun u : Sphere n => (0 : Seminorm ℝ (Space n)) u^0)-(if i=j then 1 else 0)/(n:ℝ)=0 at hh
  simp only [pow_zero,one_mul,mean_const,div_one] at hh
  exact sub_eq_zero.mp hh

/-- The matrix isotropy condition gives precisely the actual H₂ projection,
not a replacement cancellation condition. -/
lemma field_zero_harmonic {n : ℕ} (hn : 2≤n) [NeZero n] (g : Seminorm ℝ (Space n))
    (hg : g≠0) (k : ℕ) (hF : momentField g k=0) :
    (harmonicSpace n 2).starProjection (toH n
      (restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)))=0 := by
  let f : C(Sphere n,ℝ) := restrictContinuous (fun x => g x^k) ((seminorm_continuous n g).pow k)
  let c := mean (fun u : Sphere n => g u^k)
  let v := toH n f-toH n (ContinuousMap.const (Sphere n) c)
  have ho : v∈(lowSpace n)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hw
      rw [real_inner_comm,show v=toH n (f-ContinuousMap.const (Sphere n) c) by simp [v],inner_toH]
      change mean (fun u : Sphere n => (g u^k-c)*((u:Space n) i*(u:Space n) j))=0
      have hij := congrArg (fun A : Mat n => A (i,j)) hF
      change mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)/c-(if i=j then 1 else 0)/(n:ℝ)=0 at hij
      have hc : c≠0 := (mean_power_pos g hg k).ne'
      have hv := (div_eq_iff hc).mp (sub_eq_zero.mp hij)
      change _=0
      simp_rw [sub_mul]
      have hi : Integrable (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j)) (sigma n) :=
        continuous_integrable (((seminorm_continuous n g).comp continuous_subtype_val).pow k |>.mul
          (by fun_prop : Continuous (fun u : Sphere n => (u:Space n) i*(u:Space n) j)))
      have hi' : Integrable (fun u : Sphere n => c*((u:Space n) i*(u:Space n) j)) (sigma n) :=
        continuous_integrable (by fun_prop)
      rw [mean,integral_sub hi hi',integral_const_mul]
      change mean (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j))-c*mean (coordinateProduct n i j)=0
      rw [coordinateProduct_mean]
      have he : mean (fun u : Sphere n => g u^k*((u:Space n) i*(u:Space n) j))=
          mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j) := by congr 1;funext u;ring
      rw [he,hv]; ring
    | zero => simp
    | add x y _ _ hx hy => simp only [inner_add_left,hx,hy,add_zero]
    | smul a x _ hx => simp only [inner_smul_left,conj_trivial,hx,mul_zero]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  simp only [sub_zero]
  have hvol := (Submodule.mem_orthogonal _ _).mp ho w (harmonicSpace_two_le_lowSpace n hw)
  have hconst : ⟪toH n (ContinuousMap.const (Sphere n) c),w⟫=0 :=
    harmonic_inner_ne hn (d := 0) (by decide) (constant_mem_harmonicSpace_zero n c) hw
  change ⟪toH n f,w⟫=0
  dsimp only [v] at hvol
  have hconst' : ⟪w,toH n (ContinuousMap.const (Sphere n) c)⟫=0 :=
    (real_inner_comm _ _).trans hconst
  rw [inner_sub_right,hconst',sub_zero] at hvol
  exact (real_inner_comm _ _).trans hvol
end PettyProjection.Position
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
namespace RelativeGauge
variable {n : ℕ} [NeZero n]

def IsMinimizer (μ : Measure (Space n)) (b : Bool) (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) : Prop :=
  supportFunctional μ g.body=1 ∧
    ∀ q : RelativeGauge (⊤ : Submodule ℝ (Space n)),supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm

omit [NeZero n] in
lemma copy_minimizer {V : Submodule ℝ (Space n)} (hV : V=⊤)
    {μ : Measure (Space n)} {b : Bool} (g : RelativeGauge V)
    (hgn : supportFunctional μ g.body=1)
    (hmin : ∀ q : RelativeGauge V,supportFunctional μ q.body=1 →
      Spherical.objective b g.toSeminorm≤Spherical.objective b q.toSeminorm) :
    ∃ f : RelativeGauge (⊤ : Submodule ℝ (Space n)),f.toSeminorm=g.toSeminorm ∧ IsMinimizer μ b f := by
  subst V
  exact ⟨g,rfl,hgn,hmin⟩

/-- Actual full-dimensional position of the logarithmic/linear optimizer,
with no determinant normalization needed in the later weighted assembly. -/
theorem exists_symmetric_position {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x) :
    ∃ T : Space n ≃L[ℝ] Space n,T.toLinearMap.IsSymmetric ∧
      ∃ g : RelativeGauge (⊤ : Submodule ℝ (Space n)),IsMinimizer (μ.map T) (regime n) g ∧
        Position.momentField g.toSeminorm (Scalar.exponent n)=0 := by
  obtain ⟨A,hinj,hF⟩ := Position.exists_optimizer_position hμ hq (regime n) (exponent_pos n)
  have hsurj : Function.Surjective (Position.op A.val) :=
    LinearMap.surjective_of_injective (f := (Position.op A.val).toLinearMap) hinj
  have hfull : LinearMap.range (Position.op A.val).toLinearMap=⊤ := LinearMap.range_eq_top.mpr hsurj
  let T : Space n ≃L[ℝ] Space n :=
    (LinearEquiv.ofBijective (Position.op A.val).toLinearMap ⟨hinj,hsurj⟩).toContinuousLinearEquiv
  obtain ⟨g,hg,hmin⟩ := copy_minimizer hfull (optimizer hμ hq (regime n) (Position.domainMap A))
    (optimizer_normalized hμ hq (regime n) (Position.domainMap A))
    (optimizer_minimal hμ hq (regime n) (Position.domainMap A))
  refine ⟨T,Position.symmetric_op A.property.1.1,g,hmin,?_⟩
  rw [hg]
  exact hF

lemma exists_full_minimizer {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0 < cosineSeminorm μ hμ x) (b : Bool) :
    ∃ g : RelativeGauge (⊤ : Submodule ℝ (Space n)),IsMinimizer μ b g :=
  exists_minimizer hμ top_ne_bot (fun x _ hx => hq x hx) b

end RelativeGauge
end PettyProjection
end

end OAI
