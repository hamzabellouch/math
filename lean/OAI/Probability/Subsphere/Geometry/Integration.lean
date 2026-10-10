import Mathlib
import OAI.Probability.Subsphere.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma introducing_radius :
    MeasurePreserving
      (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.val • z.1.val)
      ((volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)))
      volume := by
  have h₁ := MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    ((volume : Measure E).measurePreserving_homeomorphUnitSphereProd)
  have h₂ := measurePreserving_subtype_coe (μa := (volume : Measure E))
    (measurableSet_singleton (0 : E)).compl
  rw [Measure.restrict_eq_self_of_ae_mem] at h₂
  · exact h₂.comp h₁
  · exact ae_iff.mpr (by simp)

lemma lintegral_polar (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂(volume : Measure E)) =
    ∫⁻ s : Metric.sphere (0 : E) 1, ∫⁻ r : Ioi (0 : ℝ), f (r.val • s.val)
      ∂Measure.volumeIoiPow (Module.finrank ℝ E-1) ∂(volume : Measure E).toSphere := by
  rw [← introducing_radius.lintegral_comp hf]
  exact lintegral_prod _ (hf.comp introducing_radius.measurable).aemeasurable

omit [Nontrivial E] in
lemma orthogonal_sum_volume (H : Submodule ℝ E) :
    MeasurePreserving (fun z : H × Hᗮ => (z.1 : E)+(z.2 : E))
      ((volume : Measure H).prod (volume : Measure Hᗮ)) volume := by
  exact H.orthogonalDecomposition.symm.measurePreserving.comp
    (WithLp.volume_preserving_toLp H Hᗮ)

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def unitDirection (x : E) (hx : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize x,mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩

def radial (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  by
    classical
    exact if hx : x = 0 then 0 else g (unitDirection x hx)

omit [Nontrivial E] in
lemma measurable_radial {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) :
    Measurable (radial g) := by
  classical
  apply measurable_of_measurable_on_compl_singleton (0 : E)
  change Measurable (fun x : ({0}ᶜ : Set E) => radial g x.val)
  have he : (fun x : ({0}ᶜ : Set E) => radial g x.val) =
      fun x => g ((homeomorphUnitSphereProd E x).1) := by
    ext x
    have hx : x.val ≠ 0 := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using x.property
    rw [radial,dite_eq_right hx]
    congr 1
    apply Subtype.ext
    simp [unitDirection, NormedSpace.normalize]
  rw [he]
  exact hg.comp (measurable_fst.comp (homeomorphUnitSphereProd E).measurable)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma radial_smul (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (s : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) : radial g (r • s.val) = g s := by
  have hs : s.val ≠ 0 := by
    intro hs
    have hn := mem_sphere_zero_iff_norm.mp s.property
    rw [hs,norm_zero] at hn
    norm_num at hn
  rw [radial,dite_eq_right (smul_ne_zero hr.ne' hs)]
  congr 1
  apply Subtype.ext
  exact (NormedSpace.normalize_smul_of_pos hr _).trans
    (NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp s.property))

lemma radial_ball_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in Metric.ball (0 : E) 1, radial g x ∂volume) =
      (volume (Metric.ball (0 : E) 1)) * ∫⁻ s, g s ∂Affine.sphereLaw E := by
  classical
  let d := Module.finrank ℝ E
  have hd : 0 < d := Module.finrank_pos
  have hm : Measurable ((Metric.ball (0 : E) 1).indicator (radial g)) :=
    (measurable_radial hg).indicator Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,lintegral_polar _ hm]
  have he (s : Metric.sphere (0 : E) 1) :
      (fun r : Ioi (0 : ℝ) => (Metric.ball (0 : E) 1).indicator (radial g) (r.val • s.val)) =
        (Iio (⟨1,by norm_num⟩ : Ioi (0 : ℝ))).indicator (fun _ => g s) := by
    ext r
    have hn : ‖r.val • s.val‖ = r.val := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
        mem_sphere_zero_iff_norm.mp s.property,mul_one]
    simp only [Set.indicator_apply,Metric.mem_ball,dist_zero_right,hn,Set.mem_Iio,
      radial_smul g s r.property]
    rfl
  simp_rw [he,lintegral_indicator_const measurableSet_Iio,
    Measure.volumeIoiPow_apply_Iio]
  have hed : Module.finrank ℝ E - 1 + 1 = d := Nat.sub_add_cancel hd
  simp only [hed, one_pow]
  have hrd : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hed
  rw [hrd]
  rw [lintegral_mul_const]
  rw [Affine.sphereLaw,lintegral_smul_measure,Measure.toSphere_apply_univ]
  have hv0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hd : (0 : ℝ) < d),
    ENNReal.ofReal_natCast, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top _))]
  calc
    _ = (d : ℝ≥0∞)⁻¹ * ∫⁻ s, g s ∂(volume : Measure E).toSphere := mul_comm _ _
    _ = (volume (Metric.ball (0 : E) 1) * ((d : ℝ≥0∞)⁻¹ * (volume (Metric.ball (0 : E) 1))⁻¹)) *
        ∫⁻ s, g s ∂(volume : Measure E).toSphere := by
      congr 1
      rw [mul_left_comm, ENNReal.mul_inv_cancel hv0 hvt, mul_one]
    _ = _ := by rw [mul_assoc]
  all_goals exact hg

end SubsphereCurrent.Polar
end
end
section
/-! Isometric naturality of the exact normalized Haar spherical law. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
noncomputable section
namespace SubsphereCurrent.Polar
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def sphereMap (e : E ≃ₗᵢ[ℝ] F) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 :=
  e.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere_zero_iff_norm]
    exact (e.norm_map x).symm ▸ Iff.rfl)

lemma sphereMap_preserving (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereMap e) (Affine.sphereLaw E) (Affine.sphereLaw F) := by
  have hc (s : Set (Metric.sphere (0 : F) 1)) :
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereMap e) ⁻¹' s)) =
        e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,_,⟨y,hy,rfl⟩,rfl⟩
      exact ⟨r,hr,_,⟨sphereMap e y,hy,rfl⟩, by change r • e y.val = e (r • y.val); simp⟩
    · rintro ⟨r,hr,_,⟨y,hy,rfl⟩,he⟩
      refine ⟨r,hr,_,⟨(sphereMap e).symm y,?_,rfl⟩,?_⟩
      · simpa using hy
      · apply e.injective
        change e (r • e.symm y.val) = e x
        simpa using he
  have hsphere : (volume : Measure E).toSphere.map (sphereMap e) =
      (volume : Measure F).toSphere := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply (sphereMap e).measurable hs,
      Measure.toSphere_apply' _ ((sphereMap e).measurable hs),
      Measure.toSphere_apply' _ hs,hc]
    rw [e.toLinearEquiv.finrank_eq]
    congr 1
    rw [← e.measurePreserving.map_eq]
    exact (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
  have huniv : (volume : Measure E).toSphere univ = (volume : Measure F).toSphere univ := by
    rw [← hsphere,Measure.map_apply (sphereMap e).measurable MeasurableSet.univ]
    rfl
  refine ⟨(sphereMap e).measurable,?_⟩
  rw [Affine.sphereLaw, Measure.map_smul _ (sphereMap e).measurable.aemeasurable,
    hsphere, huniv, Affine.sphereLaw]

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

structure Test (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) where
  space : Submodule ℝ E
  dimension : Module.finrank ℝ space = k
  center : E
  perpendicular : center ∈ spaceᗮ
  radius : ℝ
  positive : 0 < radius
  unit : ‖center‖^2 + radius^2 = 1

def Test.point {k : ℕ} (A : Test E k) (s : Metric.sphere (0 : A.space) 1) : Metric.sphere (0 : E) 1 := by
  refine ⟨A.center+A.radius • (s.val : E),mem_sphere_zero_iff_norm.mpr ?_⟩
  have ho : ⟪A.center,(s.val : E)⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal s.val.property A.perpendicular
  have hs : ‖(s.val : E)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  have hh : ‖A.center+A.radius • (s.val : E)‖^2 = 1 := by
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.positive,hs,mul_one]
    nlinarith [A.unit]
  nlinarith [norm_nonneg (A.center+A.radius • (s.val : E))]

lemma Test.measurable_point {k : ℕ} (A : Test E k) : Measurable A.point := by
  exact (measurable_const.add (measurable_const.smul
    (measurable_subtype_coe.comp measurable_subtype_coe))).subtype_mk

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma orthogonal_radius_norm (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (s : Metric.sphere (0 : K) 1) (r : ℝ) :
    ‖x+r • (s.val : E)‖^2 = ‖x‖^2+r^2 := by
  have ho : ⟪x,(s.val : E)⟫ = 0 := Submodule.inner_left_of_mem_orthogonal s.val.property hx
  have hs : ‖(s.val : E)‖ = 1 := by
    rw [Submodule.norm_coe]
    exact mem_sphere_zero_iff_norm.mp s.property
  rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,hs,mul_one,
    Real.norm_eq_abs,sq_abs]
  ring

def radiusNorm (x : E) (r : ℝ) : ℝ := Real.sqrt (‖x‖^2+r^2)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radiusNorm_pos (x : E) {r : ℝ} (hr : 0 < r) : 0 < radiusNorm x r := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg ‖x‖,sq_pos_of_pos hr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma radiusNorm_sq (x : E) (r : ℝ) : radiusNorm x r ^ 2 = ‖x‖^2+r^2 :=
  Real.sq_sqrt (by positivity)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_eq_radiusNorm (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (s : Metric.sphere (0 : K) 1) (r : ℝ) : ‖x+r • (s.val : E)‖ = radiusNorm x r := by
  have h := orthogonal_radius_norm K hx s r
  have hr : 0 ≤ radiusNorm x r := Real.sqrt_nonneg _
  nlinarith [radiusNorm_sq x r, norm_nonneg (x+r • (s.val : E))]

def scaledTest (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ)
    (r : ℝ) (hr : 0 < r) : Test E (Module.finrank ℝ K) where
  space := K
  dimension := rfl
  center := (radiusNorm x r)⁻¹ • x
  perpendicular := Kᗮ.smul_mem _ hx
  radius := r / radiusNorm x r
  positive := div_pos hr (radiusNorm_pos x hr)
  unit := by
    have hp := radiusNorm_pos x hr
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    have hh := radiusNorm_sq x r
    field_simp
    nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma radial_on_slice (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (K : Submodule ℝ E) {x : E} (hx : x ∈ Kᗮ) {r : ℝ} (hr : 0 < r)
    (s : Metric.sphere (0 : K) 1) :
    Polar.radial g (x+r • (s.val : E)) = g ((scaledTest K hx r hr).point s) := by
  have hp := radiusNorm_pos x hr
  have hn := norm_eq_radiusNorm K hx s r
  have hne : x+r • (s.val : E) ≠ 0 := by
    intro he
    rw [he,norm_zero] at hn
    linarith
  rw [Polar.radial,dite_eq_right hne]
  congr 1
  apply Subtype.ext
  simp only [Polar.unitDirection,NormedSpace.normalize,hn,Test.point,scaledTest]
  rw [smul_add,smul_smul,div_eq_mul_inv,mul_comm r]

def Controlled (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (k b : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ A : Test E k, ENNReal.ofReal (A.radius^b) *
    (∫⁻ s, g (A.point s) ∂Affine.sphereLaw A.space) ≤ C

lemma radial_slice_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} {k b : ℕ} {C : ℝ≥0∞}
    (hc : Controlled g k b C) (K : Submodule ℝ E) (hK : Module.finrank ℝ K = k)
    {x : E} (hx : x ∈ Kᗮ) {r : ℝ} (hr : 0 < r) (hsmall : radiusNorm x r ≤ 1) :
    (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
      ∂Affine.sphereLaw K) ≤ C * (ENNReal.ofReal (r^b))⁻¹ := by
  let A := scaledTest K hx r hr
  have ha := hc (hK ▸ A)
  have hav : ENNReal.ofReal ((r/radiusNorm x r)^b) *
      (∫⁻ s : Metric.sphere (0 : K) 1, g (A.point s) ∂Affine.sphereLaw K) ≤ C := by
    subst k
    exact ha
  have hrr : r ≤ r/radiusNorm x r := by
    apply (le_div_iff₀ (radiusNorm_pos x hr)).2
    nlinarith
  have hmul : ENNReal.ofReal (r^b) *
      (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
        ∂Affine.sphereLaw K) ≤ C := by
    simp_rw [radial_on_slice g K hx hr]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hr.le hrr b)) le_rfl).trans hav
  have h0 : ENNReal.ofReal (r^b) ≠ 0 := by positivity
  have ht : ENNReal.ofReal (r^b) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ = (ENNReal.ofReal (r^b))⁻¹ * (ENNReal.ofReal (r^b) *
        ∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E)) ∂Affine.sphereLaw K) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ht,one_mul]
    _ ≤ (ENNReal.ofReal (r^b))⁻¹ * C := mul_le_mul' le_rfl hmul
    _ = _ := mul_comm _ _

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Weighted

def nestedSpaceEquiv {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k) :
    B.space ≃ₗᵢ[ℝ] B.space.map A.space.subtype where
  toLinearEquiv := B.space.equivMapOfInjective A.space.subtype Subtype.val_injective
  norm_map' := by intro x; rfl

@[simp] lemma nestedSpaceEquiv_val {d n k : ℕ} (A : Affine.Test d n)
    (B : Slice.Test A.space k) (x : B.space) :
    (nestedSpaceEquiv A B x : Vector d) = (x.val : Vector d) := rfl

def nestedTest {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k) : Affine.Test d k where
  space := B.space.map A.space.subtype
  dimension := (nestedSpaceEquiv A B).toLinearEquiv.finrank_eq.symm.trans B.dimension
  center := A.center + A.radius • (B.center : Vector d)
  perpendicular := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [inner_add_right,real_inner_smul_right]
    have hA : ⟪(x : Vector d),A.center⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal x.property A.perpendicular
    have hB : ⟪(x : Vector d),(B.center : Vector d)⟫ = 0 := by
      change ⟪x,B.center⟫ = 0
      exact Submodule.inner_right_of_mem_orthogonal hx B.perpendicular
    change ⟪(x : Vector d),A.center⟫ + A.radius*⟪(x : Vector d),(B.center : Vector d)⟫ = 0
    rw [hA,hB,mul_zero,add_zero]
  radius := A.radius * B.radius
  radius_positive := mul_pos A.radius_positive B.positive
  unit := by
    have ho : ⟪A.center,(B.center : Vector d)⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal B.center.property A.perpendicular
    rw [norm_add_sq_real,real_inner_smul_right,ho,mul_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos A.radius_positive,Submodule.norm_coe]
    nlinarith [A.unit, B.unit]

lemma nestedTest_point {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k)
    (s : Metric.sphere (0 : B.space) 1) :
    onTest (nestedTest A B) (@Polar.sphereMap B.space (B.space.map A.space.subtype)
      B.space.normedAddCommGroup B.space.innerProductSpace
      (B.space.map A.space.subtype).normedAddCommGroup (B.space.map A.space.subtype).innerProductSpace (nestedSpaceEquiv A B) s) =
      onTest A (B.point s) := by
  apply Subtype.ext
  change A.center+A.radius • (B.center : Vector d)+(A.radius*B.radius) • (s.val.val : Vector d) =
    A.center+A.radius • ((B.center : Vector d)+B.radius • (s.val.val : Vector d))
  rw [smul_add,smul_smul,add_assoc]

lemma borel_onTest {d n : ℕ} (A : Affine.Test d n) : Measurable (onTest A) := by
  apply Measurable.subtype_mk
  change Measurable (fun s : Affine.Sphere A.space => A.center+A.radius • (s.val : Vector d))
  fun_prop

lemma radius_le_one {d n : ℕ} (A : Affine.Test d n) : A.radius ≤ 1 := by
  nlinarith [A.unit,sq_nonneg ‖A.center‖,A.radius_positive]

lemma nested_average {d n k : ℕ} (A : Affine.Test d n) (B : Slice.Test A.space k)
    {g : Sphere d → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s, g (onTest (nestedTest A B) s) ∂Affine.sphereLaw (nestedTest A B).space) =
      ∫⁻ s, g (onTest A (B.point s)) ∂Affine.sphereLaw B.space := by
  let e : B.space ≃ₗᵢ[ℝ] (nestedTest A B).space := nestedSpaceEquiv A B
  let f := @Polar.sphereMap B.space (nestedTest A B).space
    B.space.normedAddCommGroup B.space.innerProductSpace
    (nestedTest A B).space.normedAddCommGroup (nestedTest A B).space.innerProductSpace e
  have hp := @Polar.sphereMap_preserving B.space (nestedTest A B).space
    B.space.normedAddCommGroup B.space.innerProductSpace inferInstance inferInstance inferInstance
    (nestedTest A B).space.normedAddCommGroup (nestedTest A B).space.innerProductSpace
    inferInstance inferInstance inferInstance e
  calc
    _ = ∫⁻ s, g (onTest (nestedTest A B) (f s)) ∂Affine.sphereLaw B.space := by
      exact (hp.lintegral_comp (hg.comp (borel_onTest (nestedTest A B)))).symm
    _ = _ := by
      apply lintegral_congr
      intro s
      congr 1
      exact nestedTest_point A B s

end SubsphereCurrent.Weighted
end
end
section
open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent.Polar

lemma radius_inverse_density (k b : ℕ) (hb : b+1 ≤ k) :
    (Measure.volumeIoiPow (k-1)).withDensity
      (fun r : Ioi (0 : ℝ) => (ENNReal.ofReal (r.val^b))⁻¹) =
        Measure.volumeIoiPow (k-b-1) := by
  rw [Measure.volumeIoiPow,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  ext r
  have hr : 0 < r.val := r.property
  change ENNReal.ofReal (r.val^(k-1)) * (ENNReal.ofReal (r.val^b))⁻¹ =
    ENNReal.ofReal (r.val^(k-b-1))
  have hn : k-1 = (k-b-1)+b := by omega
  rw [hn,pow_add,ENNReal.ofReal_mul (by positivity),mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,mul_one]

lemma radius_inverse_integral (k b : ℕ) (hb : b+1 ≤ k) {t : ℝ} (ht : 0 < t) :
    (∫⁻ r in Iio (⟨t,ht⟩ : Ioi (0 : ℝ)), (ENNReal.ofReal (r.val^b))⁻¹
      ∂Measure.volumeIoiPow (k-1)) = ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) := by
  rw [← withDensity_apply _ measurableSet_Iio,radius_inverse_density k b hb,
    Measure.volumeIoiPow_apply_Iio]
  have hn : k-b-1+1 = k-b := by omega
  rw [hn]
  congr 2
  exact_mod_cast hn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma orthogonal_volume_ratio (K : Submodule ℝ E) :
    (volume : Measure K) (Metric.ball 0 1) *
      (volume : Measure Kᗮ) (Metric.ball 0 1) ≤
        (2 : ℝ≥0∞)^Module.finrank ℝ E * (volume : Measure E) (Metric.ball 0 1) := by
  have hp := orthogonal_sum_volume K
  have hsub : (Metric.ball (0 : K) (1/2)) ×ˢ (Metric.ball (0 : Kᗮ) (1/2)) ⊆
      (fun z : K × Kᗮ => (z.1 : E)+(z.2 : E)) ⁻¹' Metric.ball 0 1 := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    change dist ((x : E)+(y : E)) 0 < 1
    simp only [Metric.mem_ball,dist_zero_right] at hx hy ⊢
    have hh := norm_add_le (x : E) (y : E)
    change ‖(x : E)+(y : E)‖ < 1
    have hx' : ‖(x : E)‖ < 1/2 := hx
    have hy' : ‖(y : E)‖ < 1/2 := hy
    linarith
  have hm := measure_mono (μ := (volume : Measure K).prod (volume : Measure Kᗮ)) hsub
  rw [Measure.prod_prod,hp.measure_preimage Metric.isOpen_ball.measurableSet.nullMeasurableSet] at hm
  rw [Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2),
      Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1/2)] at hm
  have hd := K.finrank_add_finrank_orthogonal
  have he : ENNReal.ofReal ((1/2 : ℝ)^Module.finrank ℝ K) *
      ENNReal.ofReal ((1/2 : ℝ)^Module.finrank ℝ Kᗮ) =
      ((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity),← pow_add,hd,
      ENNReal.ofReal_pow (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num [ENNReal.inv_pow]
  have hh : ((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ *
      ((volume : Measure K) (Metric.ball 0 1) * (volume : Measure Kᗮ) (Metric.ball 0 1)) ≤
        (volume : Measure E) (Metric.ball 0 1) := by
    rw [← he]
    convert hm using 1
    ring
  have h0 : (2 : ℝ≥0∞)^Module.finrank ℝ E ≠ 0 := by positivity
  have ht : (2 : ℝ≥0∞)^Module.finrank ℝ E ≠ ∞ := by finiteness
  calc
    _ = (2 : ℝ≥0∞)^Module.finrank ℝ E *
        (((2 : ℝ≥0∞)^Module.finrank ℝ E)⁻¹ *
          ((volume : Measure K) (Metric.ball 0 1) * (volume : Measure Kᗮ) (Metric.ball 0 1))) := by
      rw [← mul_assoc,ENNReal.mul_inv_cancel h0 ht,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hh

end SubsphereCurrent.Polar
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma sphere_integral_unnormalize (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) :
    (∫⁻ s, g s ∂(volume : Measure E).toSphere) =
      ((volume : Measure E).toSphere univ) * (∫⁻ s, g s ∂Affine.sphereLaw E) := by
  have h0 : (volume : Measure E).toSphere univ ≠ 0 := by
    intro h
    exact Measure.toSphere_ne_zero volume (Measure.measure_univ_eq_zero.mp h)
  have ht : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  rw [Affine.sphereLaw,lintegral_smul_measure,smul_eq_mul,← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht,one_mul]

def capFunction (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ)
    (s : Metric.sphere (0 : E) 1) : ℝ≥0∞ :=
  if dist s.val z ≤ t then g s else 0

def ballCap (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ) : E → ℝ≥0∞ :=
  (Metric.ball (0 : E) 1).indicator (Polar.radial (capFunction g z t))

omit [Nontrivial E] in
lemma measurable_capFunction {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : Measurable g) (z : E) (t : ℝ) : Measurable (capFunction g z t) :=
  Measurable.ite (measurableSet_le (by fun_prop) measurable_const) hg measurable_const

omit [Nontrivial E] in
lemma measurable_ballCap {g : Metric.sphere (0 : E) 1 → ℝ≥0∞}
    (hg : Measurable g) (z : E) (t : ℝ) : Measurable (ballCap g z t) :=
  (Polar.measurable_radial (measurable_capFunction hg z t)).indicator Metric.isOpen_ball.measurableSet

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma ballCap_le (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) (z : E) (t : ℝ) (x : E) :
    ballCap g z t x ≤ Polar.radial g x := by
  classical
  apply (Set.indicator_le_self _ _ _).trans
  by_cases hx : x = 0
  · simp [Polar.radial,hx]
  · rw [Polar.radial,dite_eq_right hx,Polar.radial,dite_eq_right hx]
    unfold capFunction
    split_ifs <;> simp

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma ballCap_support (g : Metric.sphere (0 : E) 1 → ℝ≥0∞)
    (K : Submodule ℝ E) {z x : E} (hz : z ∈ Kᗮ) (hx : x ∈ Kᗮ)
    {r t : ℝ} (hr : 0 < r) (s : Metric.sphere (0 : K) 1)
    (hnz : ballCap g z t (x+r • (s.val : E)) ≠ 0) :
    ‖x‖ < 1 ∧ r < t ∧ radiusNorm x r < 1 := by
  classical
  have hn := norm_eq_radiusNorm K hx s r
  have hp := radiusNorm_pos x hr
  have hne : x+r • (s.val : E) ≠ 0 := by
    intro hh
    rw [hh,norm_zero] at hn
    linarith
  have hball : x+r • (s.val : E) ∈ Metric.ball (0 : E) 1 := by
    by_contra hh
    exact hnz (Set.indicator_of_notMem hh _)
  have hb : radiusNorm x r < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right,hn] using hball
  have hcap : dist (Polar.unitDirection (x+r • (s.val : E)) hne).val z ≤ t := by
    by_contra hh
    apply hnz
    rw [ballCap,Set.indicator_of_mem hball,Polar.radial,dite_eq_right hne,capFunction,
      ite_eq_right hh]
  have hx' : ‖x‖ < 1 := by
    have hh := radiusNorm_sq x r
    nlinarith [norm_nonneg x,sq_nonneg r]
  have hproj : K.orthogonalProjectionOnto
      ((Polar.unitDirection (x+r • (s.val : E)) hne).val-z) =
        ((radiusNorm x r)⁻¹*r) • s.val := by
    simp only [Polar.unitDirection,NormedSpace.normalize,hn,map_sub,map_smul,map_add,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,zero_add,sub_zero,smul_smul]
  have hl := K.norm_orthogonalProjectionOnto_apply_le
    ((Polar.unitDirection (x+r • (s.val : E)) hne).val-z)
  rw [hproj,norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (inv_pos.mpr hp) hr),
    mem_sphere_zero_iff_norm.mp s.property,mul_one] at hl
  rw [dist_eq_norm] at hcap
  have hrt : r < t := by
    have hr' : r < (radiusNorm x r)⁻¹*r := by
      have : 1 < (radiusNorm x r)⁻¹ := (one_lt_inv₀ hp).2 hb
      nlinarith
    exact hr'.trans_le (hl.trans hcap)
  exact ⟨hx',hrt,hb⟩

omit [Nontrivial E] in
lemma angular_ballCap_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} {k b : ℕ} {C : ℝ≥0∞}
    (hc : Controlled g k b C) (K : Submodule ℝ E) [Nontrivial K]
    (hK : Module.finrank ℝ K = k) {z x : E} (hz : z ∈ Kᗮ) (hx : x ∈ Kᗮ)
    {r t : ℝ} (hr : 0 < r) :
    (∫⁻ s : Metric.sphere (0 : K) 1, ballCap g z t (x+r • (s.val : E))
      ∂(volume : Measure K).toSphere) ≤
        (if ‖x‖ < 1 ∧ r < t then
          ((volume : Measure K).toSphere univ) * C * (ENNReal.ofReal (r^b))⁻¹ else 0) := by
  classical
  by_cases hh : ‖x‖ < 1 ∧ r < t
  · rw [ite_eq_left hh]
    by_cases hs : radiusNorm x r < 1
    · calc
        _ ≤ ∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
            ∂(volume : Measure K).toSphere := lintegral_mono fun s => ballCap_le _ _ _ _
        _ = (volume : Measure K).toSphere univ *
            (∫⁻ s : Metric.sphere (0 : K) 1, Polar.radial g (x+r • (s.val : E))
              ∂Affine.sphereLaw K) := sphere_integral_unnormalize _
        _ ≤ (volume : Measure K).toSphere univ * (C * (ENNReal.ofReal (r^b))⁻¹) :=
          mul_le_mul' le_rfl (radial_slice_bound hc K hK hx hr hs.le)
        _ = _ := (mul_assoc _ _ _).symm
    · have he (s : Metric.sphere (0 : K) 1) : ballCap g z t (x+r • (s.val : E)) = 0 := by
        by_contra hnz
        exact hs (ballCap_support g K hz hx hr s hnz).2.2
      simp only [he,lintegral_zero,zero_le]
  · rw [ite_eq_right hh]
    have he (s : Metric.sphere (0 : K) 1) : ballCap g z t (x+r • (s.val : E)) = 0 := by
      by_contra hnz
      have hp := ballCap_support g K hz hx hr s hnz
      exact hh ⟨hp.1,hp.2.1⟩
    simp only [he,lintegral_zero,le_refl]

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Slice
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
lemma ballCap_integral {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ y : E, ballCap g z t y ∂volume) ≤
      ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) *
          (volume : Measure Kᗮ) (Metric.ball 0 1) := by
  classical
  have hcb := measurable_ballCap hg z t
  have hf : Measurable (fun w : K × Kᗮ => ballCap g z t ((w.1 : E)+(w.2 : E))) :=
    hcb.comp ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd))
  rw [← (Polar.orthogonal_sum_volume K).lintegral_comp hcb,
    lintegral_prod_symm _ hf.aemeasurable]
  have hi (x : Kᗮ) :
      (∫⁻ y : K, ballCap g z t ((y : E)+(x : E)) ∂volume) ≤
      (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) := by
    have hym : Measurable (fun y : K => ballCap g z t ((y : E)+(x : E))) :=
      hcb.comp (measurable_subtype_coe.add measurable_const)
    have hpm : Measurable (fun w : Metric.sphere (0 : K) 1 × Ioi (0 : ℝ) =>
        ballCap g z t ((w.2.val • w.1.val : K)+(x : E))) := by
      apply hcb.comp
      fun_prop
    rw [← (Polar.introducing_radius (E := K)).lintegral_comp hym,
      lintegral_prod_symm _ hpm.aemeasurable]
    calc
      _ ≤ ∫⁻ r : Ioi (0 : ℝ), (if ‖(x : E)‖ < 1 ∧ r.val < t then
          (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹ else 0)
          ∂Measure.volumeIoiPow (k-1) := by
        rw [hK]
        apply lintegral_mono
        intro r
        have hh := angular_ballCap_bound hc K hK hz x.property r.property (t := t)
        simpa only [Submodule.coe_smul,add_comm (x : E)] using hh
      _ = (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
          ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) := by
        by_cases hx : ‖x‖ < 1
        · simp only [Submodule.norm_coe,hx,true_and,ite_true]
          have he : (fun r : Ioi (0 : ℝ) => if r.val < t then
              (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹ else 0) =
              (Iio (⟨t,ht⟩ : Ioi (0 : ℝ))).indicator
                (fun r => (volume : Measure K).toSphere univ * C * (ENNReal.ofReal (r.val^b))⁻¹) := by
            ext r
            simp only [Set.indicator_apply,Set.mem_Iio]
            rfl
          rw [he,lintegral_indicator measurableSet_Iio,lintegral_const_mul _ (by fun_prop),
            Polar.radius_inverse_integral k b hb ht]
        · simp only [Submodule.norm_coe,hx,false_and,ite_false,lintegral_zero]
  calc
    _ ≤ ∫⁻ x : Kᗮ, (if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
        ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) ∂volume := lintegral_mono hi
    _ = _ := by
      have he : (fun x : Kᗮ => if ‖x‖ < 1 then ((volume : Measure K).toSphere univ) * C *
          ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)) else 0) =
          (Metric.ball (0 : Kᗮ) 1).indicator (fun _ => ((volume : Measure K).toSphere univ) * C *
            ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ))) := by
        ext x
        simp only [Set.indicator_apply,Metric.mem_ball,dist_zero_right]
      rw [he,lintegral_indicator_const Metric.isOpen_ball.measurableSet]

omit [Nontrivial E] in
lemma radius_mass_le (K : Submodule ℝ E) {b : ℕ} (hb : b+1 ≤ Module.finrank ℝ K)
    (h2b : 2*b ≤ Module.finrank ℝ K) {t : ℝ} (ht : 0 < t) :
    ((volume : Measure K).toSphere univ) *
      ENNReal.ofReal (t^(Module.finrank ℝ K-b)/((Module.finrank ℝ K-b : ℕ) : ℝ)) ≤
        2 * (volume : Measure K) (Metric.ball 0 1) * ENNReal.ofReal (t^(Module.finrank ℝ K-b)) := by
  let k := Module.finrank ℝ K
  have hkb : (0 : ℝ) < (k-b : ℕ) := by exact_mod_cast (by dsimp [k]; omega : 0 < k-b)
  have hratio : (k : ℝ) * (t^(k-b)/((k-b : ℕ) : ℝ)) ≤ 2*t^(k-b) := by
    have hk : (k : ℝ) ≤ 2*(k-b : ℕ) := by exact_mod_cast (by dsimp [k]; omega : k ≤ 2*(k-b))
    rw [← mul_div_assoc,div_le_iff₀ hkb]
    have h := mul_le_mul_of_nonneg_right hk (pow_nonneg ht.le (k-b))
    nlinarith [h]
  rw [Measure.toSphere_apply_univ]
  calc
    _ = (volume : Measure K) (Metric.ball 0 1) *
        ENNReal.ofReal ((k : ℝ)*(t^(k-b)/((k-b : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
      ring
    _ ≤ (volume : Measure K) (Metric.ball 0 1) * ENNReal.ofReal (2*t^(k-b)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hratio)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num; ring

lemma controlled_cap_bound {g : Metric.sphere (0 : E) 1 → ℝ≥0∞} (hg : Measurable g)
    {k b : ℕ} {C : ℝ≥0∞} (hc : Controlled g k b C)
    (K : Submodule ℝ E) [Nontrivial K] (hK : Module.finrank ℝ K = k)
    (hb : b+1 ≤ k) (h2b : 2*b ≤ k) {z : E} (hz : z ∈ Kᗮ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ s, capFunction g z t s ∂Affine.sphereLaw E) ≤
      (2 : ℝ≥0∞)^(Module.finrank ℝ E+1) * C * ENNReal.ofReal (t^(k-b)) := by
  have hball := Polar.radial_ball_integral (measurable_capFunction hg z t)
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet] at hball
  change (∫⁻ y : E, ballCap g z t y ∂volume) = _ at hball
  have hh := ballCap_integral hg hc K hK hb hz ht
  rw [hball] at hh
  have hmass := radius_mass_le K (by simpa only [hK] using hb) (by simpa only [hK] using h2b) ht
  rw [hK] at hmass
  have hratio := Polar.orthogonal_volume_ratio K
  have hv0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hfinal : (volume : Measure E) (Metric.ball 0 1) *
      (∫⁻ s, capFunction g z t s ∂Affine.sphereLaw E) ≤
      (volume : Measure E) (Metric.ball 0 1) *
        ((2 : ℝ≥0∞)^(Module.finrank ℝ E+1)*C*ENNReal.ofReal (t^(k-b))) := by
    calc
      _ ≤ (volume : Measure K).toSphere univ*C*ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ))*
          (volume : Measure Kᗮ) (Metric.ball 0 1) := hh
      _ = ((volume : Measure K).toSphere univ*ENNReal.ofReal (t^(k-b)/((k-b : ℕ) : ℝ)))*
          C*(volume : Measure Kᗮ) (Metric.ball 0 1) := by ring
      _ ≤ (2*(volume : Measure K) (Metric.ball 0 1)*ENNReal.ofReal (t^(k-b)))*
          C*(volume : Measure Kᗮ) (Metric.ball 0 1) := by gcongr
      _ = ((volume : Measure K) (Metric.ball 0 1)*(volume : Measure Kᗮ) (Metric.ball 0 1))*
          (2*C*ENNReal.ofReal (t^(k-b))) := by ring
      _ ≤ ((2 : ℝ≥0∞)^Module.finrank ℝ E*(volume : Measure E) (Metric.ball 0 1))*
          (2*C*ENNReal.ofReal (t^(k-b))) := mul_le_mul' hratio le_rfl
      _ = _ := by rw [pow_succ]; ring
  exact (ENNReal.mul_le_mul_iff_right hv0 hvt).mp hfinal

end SubsphereCurrent.Slice
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Quarter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def twinTurn (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    WithLp 2 (F × F) ≃ₗᵢ[ℝ] WithLp 2 (F × F) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ F F).trans
    ((LinearIsometryEquiv.neg ℝ).withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ F))

lemma twinTurn_inner (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : WithLp 2 (F × F)) : ⟪x,twinTurn F x⟫ = 0 := by
  simp only [twinTurn, LinearIsometryEquiv.trans_apply, WithLp.prod_inner_apply]
  change ⟪x.ofLp.1,-x.ofLp.2⟫ + ⟪x.ofLp.2,x.ofLp.1⟫ = 0
  rw [inner_neg_right,real_inner_comm x.ofLp.2 x.ofLp.1]
  ring

lemma twinTurn_square (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x : WithLp 2 (F × F)) : twinTurn F (twinTurn F x) = -x := by
  apply WithLp.ofLp_injective
  change (-x.ofLp.1,-x.ofLp.2) = (-x).ofLp
  rfl

lemma exists_even_turn {k : ℕ} (hk : Module.finrank ℝ E = k+k) :
    ∃ e : E ≃ₗᵢ[ℝ] E, (∀ x, ⟪x,e x⟫ = 0) ∧ (∀ x, e (e x) = -x) := by
  let b := (stdOrthonormalBasis ℝ E).reindex ((finCongr hk).trans finSumFinEquiv.symm)
  let f : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    b.repr.trans (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin k ⊕ Fin k => ℝ))
  let e := (f.trans (twinTurn (EuclideanSpace ℝ (Fin k)))).trans f.symm
  refine ⟨e, ?_, ?_⟩
  · intro x
    rw [← f.inner_map_map]
    simpa [e] using twinTurn_inner (EuclideanSpace ℝ (Fin k)) (f x)
  · intro x
    apply f.injective
    simp [e, twinTurn_square]

omit [FiniteDimensional ℝ E] in
lemma subspace_dimension (U : Submodule ℝ E) {k : ℕ} (hk : k ≤ Module.finrank ℝ U) :
    ∃ F : Submodule ℝ E, F ≤ U ∧ Module.finrank ℝ F = k := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank (R := ℝ) (M := U) hk
  let w : Fin k → E := fun i => v i
  have hw : LinearIndependent ℝ w := hv.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨Submodule.span ℝ (Set.range w), ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact (v i).property)
  · simpa using finrank_span_eq_card hw

lemma exists_small_fixed (U : Submodule ℝ E) :
    ∃ F : Submodule ℝ E, F ≤ Uᗮ ∧
      Module.finrank ℝ Fᗮ ≤ Module.finrank ℝ U + 1 ∧
      ∃ e : F ≃ₗᵢ[ℝ] F, (∀ x, ⟪x,e x⟫ = 0) ∧ (∀ x, e (e x) = -x) := by
  let k := Module.finrank ℝ Uᗮ / 2
  obtain ⟨F,hFU,hF⟩ := subspace_dimension Uᗮ (k := k+k) (by dsimp [k]; omega)
  refine ⟨F,hFU,?_,exists_even_turn hF⟩
  have hU := U.finrank_add_finrank_orthogonal
  have hF' := F.finrank_add_finrank_orthogonal
  dsimp [k] at hF
  omega

def extend (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) : E ≃ₗᵢ[ℝ] E :=
  (F.orthogonalDecomposition.trans
    (e.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ Fᗮ))).trans F.orthogonalDecomposition.symm

lemma extend_apply (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) (x : E) :
    extend F e x = (e (F.orthogonalProjectionOnto x) : E) + Fᗮ.starProjection x := by
  simp [extend, Submodule.orthogonalDecomposition_symm_apply]

lemma extend_fixed (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) {x : E} (hx : x ∈ Fᗮ) :
    extend F e x = x := by
  rw [extend_apply, F.orthogonalProjectionOnto_apply_of_mem_orthogonal hx]
  simp [Submodule.starProjection_eq_self_iff.mpr hx]

lemma extend_norm_sq (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F) (he : ∀ y, ⟪y,e y⟫ = 0)
    (x : E) : dist x (extend F e x)^2 = 2*‖F.orthogonalProjectionOnto x‖^2 := by
  rw [← F.orthogonalDecomposition.dist_map]
  simp only [extend, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply]
  simp only [Submodule.orthogonalDecomposition_apply,
    LinearIsometryEquiv.withLpProdCongr_apply,
    WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub]
  change ⟪F.orthogonalProjectionOnto x-e (F.orthogonalProjectionOnto x),
    F.orthogonalProjectionOnto x-e (F.orthogonalProjectionOnto x)⟫ + ⟪Fᗮ.orthogonalProjectionOnto x-Fᗮ.orthogonalProjectionOnto x,
      Fᗮ.orthogonalProjectionOnto x-Fᗮ.orthogonalProjectionOnto x⟫ = _
  rw [sub_self,inner_zero_left,add_zero,inner_sub_left,inner_sub_right,inner_sub_right,
    he,real_inner_comm (F.orthogonalProjectionOnto x) (e (F.orthogonalProjectionOnto x)),he,e.inner_map_map,real_inner_self_eq_norm_sq]
  ring

lemma extend_square_norm_sq (F : Submodule ℝ E) (e : F ≃ₗᵢ[ℝ] F)
    (he : ∀ y, e (e y) = -y) (x : E) :
    dist x (extend F e (extend F e x))^2 = 4*‖F.orthogonalProjectionOnto x‖^2 := by
  rw [← F.orthogonalDecomposition.dist_map]
  simp only [extend, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.withLpProdCongr_apply]
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, WithLp.prod_inner_apply]
  simp only [Submodule.orthogonalDecomposition_apply,
    WithLp.ofLp_sub, Prod.fst_sub, Prod.snd_sub]
  change ⟪F.orthogonalProjectionOnto x-e (e (F.orthogonalProjectionOnto x)),
    F.orthogonalProjectionOnto x-e (e (F.orthogonalProjectionOnto x))⟫ + ⟪Fᗮ.orthogonalProjectionOnto x-Fᗮ.orthogonalProjectionOnto x,
      Fᗮ.orthogonalProjectionOnto x-Fᗮ.orthogonalProjectionOnto x⟫ = _
  rw [he,sub_neg_eq_add,sub_self,inner_zero_left,add_zero,inner_add_left,inner_add_right,
    real_inner_self_eq_norm_sq]
  ring

end SubsphereCurrent.Quarter
end
end

end OAI
