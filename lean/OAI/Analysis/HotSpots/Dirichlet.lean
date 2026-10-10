import OAI.Analysis.HotSpots.Helmholtz

namespace OAI

section DouglasLipschitzBase
noncomputable section
section ZeroLpPairingCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.LpZeroExtension
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : Set α} (hs : MeasurableSet s)

lemma integral_inner (f : Lp E 2 (μ.restrict s)) (g : α → E) :
    (∫ x, inner ℝ (linearIsometry hs f x) (g x) ∂μ) =
      ∫ x in s, inner ℝ (f x) (g x) ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [linearIsometry_ae hs f] with x hx
  rw [hx]
  by_cases hx : x ∈ s <;> simp [hx]

lemma integral_mul (f : Lp ℝ 2 (μ.restrict s)) (g : α → ℝ) :
    (∫ x, linearIsometry hs f x * g x ∂μ) = ∫ x in s, f x * g x ∂μ := by
  simpa only [RCLike.inner_apply,RCLike.conj_to_real,mul_comm] using integral_inner hs f g

lemma integrable [IsFiniteMeasure (μ.restrict s)] (f : Lp E 2 (μ.restrict s)) :
    Integrable (linearIsometry hs f : α → E) μ :=
  ((integrable_indicator_iff hs).mpr ((Lp.memLp f).integrable (by norm_num))).congr
    (linearIsometry_ae hs f).symm

end StrictHotSpots.LpZeroExtension
end ZeroLpPairingCombinedLayer

section ZeroLpWeakCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.LpZeroExtension
variable {Ω : Set Plane} (hΩ : IsOpen Ω)
lemma weak_of_neumann (lam : ℝ) (f : Lp ℝ 2 (volume.restrict Ω))
    (g : Lp Plane 2 (volume.restrict Ω))
    (hg : HasH1Gradient univ (linearIsometry hΩ.measurableSet f) (linearIsometry hΩ.measurableSet g))
    (he : ∀ v k, HasH1Gradient Ω v k →
      (∫ x in Ω, inner ℝ (g x) (k x)) = lam * (∫ x in Ω, f x * v x)) :
    PlaneWeakEquation univ lam (linearIsometry hΩ.measurableSet f) := by
  intro φ hφ hc hs
  rw [weak_laplacian_test hg hφ hc hs]
  simp only [Measure.restrict_univ]
  rw [integral_inner hΩ.measurableSet g (gradient φ),integral_mul hΩ.measurableSet f φ,
    he _ _ (HasH1Gradient.test hΩ hφ hc),neg_mul]

lemma zero_of_weak (hb : Bornology.IsBounded Ω) (lam : ℝ)
    (f : Lp ℝ 2 (volume.restrict Ω))
    (hz : PlaneWeakEquation univ lam (linearIsometry hΩ.measurableSet f)) : f = 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hint : IntegrableOn (linearIsometry hΩ.measurableSet f) univ := by
    rw [IntegrableOn,Measure.restrict_univ]
    exact integrable hΩ.measurableSet f
  have hcne : closure Ω ≠ univ := by
    intro hh
    exact (NormedSpace.unbounded_univ ℝ Plane) (hh ▸ hb.closure)
  obtain ⟨a,ha⟩ := (ne_univ_iff_exists_notMem _).mp hcne
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl a ha
  have hzero : ∀ᵐ x ∂volume, x ∈ univ → linearIsometry hΩ.measurableSet f x = 0 :=
    planeWeak_uniqueContinuation isOpen_univ isPreconnected_univ hint hz
      ⟨a,mem_univ a,ε,hε,by
        filter_upwards [linearIsometry_ae hΩ.measurableSet f] with x hx
        intro hxb
        rw [hx,indicator_of_notMem (fun hh => hsub hxb (subset_closure hh))]⟩
  have hzLp : linearIsometry hΩ.measurableSet f = 0 := by
    apply Lp.ext
    have ha : (linearIsometry hΩ.measurableSet f : Plane → ℝ) =ᵐ[volume] (fun _ => 0) :=
      hzero.mono fun _ hx => hx (mem_univ _)
    exact ha.trans (Lp.coeFn_zero _ _ _).symm
  apply (linearIsometry hΩ.measurableSet).injective
  exact hzLp.trans (map_zero _).symm

end StrictHotSpots.LpZeroExtension
end ZeroLpWeakCombinedLayer

section H10NeumannZeroCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology Laplacian
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)
local instance : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace



lemma zero_of_neumann (hb : Bornology.IsBounded Ω) (lam : ℝ) (u : H10 hΩ)
    (he : ∀ v k, HasH1Gradient Ω v k →
      (∫ x in Ω, inner ℝ (grad hΩ u x) (k x)) =
        lam * (∫ x in Ω, value hΩ u x * v x)) : value hΩ u = 0 := by
  exact LpZeroExtension.zero_of_weak hΩ hb lam (value hΩ u)
    (LpZeroExtension.weak_of_neumann hΩ lam (value hΩ u) (grad hΩ u)
      (zero_hasH1Gradient hΩ u) he)

end StrictHotSpots.H10
end H10NeumannZeroCombinedLayer

section H10DilationCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots
open DiskH10

lemma smoothTest_value_sq_global {Ω : Set Plane} (hΩ : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.value hΩ (smoothTestToH10 hΩ f)‖^2 = ∫ x, ((f : Plane → ℝ) x)^2 := by
  rw [L2Limits.norm_sq_eq_integral_sq]
  have he : (∫ x in Ω, (H10.value hΩ (smoothTestToH10 hΩ f) x)^2) =
      ∫ x in Ω, ((f : Plane → ℝ) x)^2 := by
    apply integral_congr_ae
    filter_upwards [(test_memLp (Ω := Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
    exact congrArg (fun t : ℝ => t^2) hx
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (f.property.2.2 hh)),zero_pow (by norm_num : 2 ≠ 0)]

lemma smoothTest_grad_sq_global {Ω : Set Plane} (hΩ : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.grad hΩ (smoothTestToH10 hΩ f)‖^2 = ∫ x, ‖gradient (f : Plane → ℝ) x‖^2 := by
  rw [L2VectorLimits.norm_sq_eq_integral_norm_sq]
  have he : (∫ x in Ω, ‖H10.grad hΩ (smoothTestToH10 hΩ f) x‖^2) =
      ∫ x in Ω, ‖gradient (f : Plane → ℝ) x‖^2 := by
    apply integral_congr_ae
    filter_upwards [(test_gradient_memLp (Ω := Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
    exact congrArg (fun t : Plane => ‖t‖^2) hx
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [gradient,fderiv_of_notMem_tsupport ℝ (fun hh => hx (f.property.2.2 hh)),map_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]

lemma gradient_comp_smul {f : Plane → ℝ} (hf : Differentiable ℝ f) (R : ℝ) (x : Plane) :
    gradient (fun y => f (R • y)) x = R • gradient (f : Plane → ℝ) (R • x) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hd : fderiv ℝ (fun y : Plane => f (R • y)) x =
    (fderiv ℝ (f : Plane → ℝ) (R • x)).comp (R • ContinuousLinearMap.id ℝ Plane) :=
    (hf (R • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R) |>.fderiv
  rw [hd]
  simp

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

include hR in
private lemma radius_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR

def dilateTest : smoothTestSpace Ω →ₗ[ℝ] smoothTestSpace disk where
  toFun f := ⟨fun x => (f : Plane → ℝ) (R • x), f.property.1.comp (contDiff_id.const_smul R),
    f.property.2.1.comp_homeomorph (Homeomorph.smul (Units.mk0 R (radius_pos hR).ne')),
    by
      intro x hx
      have hh : R • x ∈ Ω := f.property.2.2 (tsupport_comp_subset_preimage _ (continuous_id.const_smul R) hx)
      have ht := hb hh
      simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (radius_pos hR)] at ht
      change ‖x - 0‖ < 1
      rw [sub_zero]
      nlinarith [radius_pos hR]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma dilateTest_value_sq (f : smoothTestSpace Ω) :
    ‖value PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))‖^2 =
      (R^2)⁻¹ * ‖value hΩ (smoothTestToH10 hΩ f)‖^2 := by
  rw [smoothTest_value_sq_global,smoothTest_value_sq_global]
  change (∫ x : Plane, ((f : Plane → ℝ) (R • x))^2) = _
  have := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) (fun x => ((f : Plane → ℝ) x)^2) R
    (hR := (radius_pos hR).le)
  simpa [Plane, finrank_euclideanSpace, smul_eq_mul] using this

lemma dilateTest_grad_sq (f : smoothTestSpace Ω) :
    ‖grad PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))‖^2 =
      ‖grad hΩ (smoothTestToH10 hΩ f)‖^2 := by
  rw [smoothTest_grad_sq_global,smoothTest_grad_sq_global]
  have hd : ∀ x, gradient (dilateTest hR hb f : Plane → ℝ) x = R • gradient (f : Plane → ℝ) (R • x) :=
    gradient_comp_smul (f.property.1.differentiable (by simp)) R
  simp_rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (radius_pos hR),mul_pow]
  rw [integral_const_mul]
  have ht := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
    (fun x => ‖gradient (f : Plane → ℝ) x‖^2) R (hR := (radius_pos hR).le)
  simp only [Plane, finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul] at ht
  rw [ht]
  field_simp [(radius_pos hR).ne']

lemma dilateTest_norm (f : smoothTestSpace Ω) :
    ‖smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f)‖ ≤ ‖smoothTestToH10 hΩ f‖ := by
  have ha := dilateTest_value_sq hΩ hR hb f
  have hg := dilateTest_grad_sq hΩ hR hb f
  have hnorm1 := norm_sq PlaneGreen.diskOpen (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))
  have hnorm2 := norm_sq hΩ (smoothTestToH10 hΩ f)
  have hi : (R^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hs := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖value hΩ (smoothTestToH10 hΩ f)‖)
  nlinarith [norm_nonneg (smoothTestToH10 hΩ f),norm_nonneg (smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f))]

end H10
end StrictHotSpots
end H10DilationCombinedLayer

section CompactDominationCombinedLayer
open Set Metric
namespace StrictHotSpots
lemma compact_of_norm_dominated {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : E →L[ℝ] F) (K : E →L[ℝ] G) (hK : IsCompactOperator K)
    {C : ℝ} (hC : 0 < C) (h : ∀ x, ‖J x‖ ≤ C * ‖K x‖) : IsCompactOperator J := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall J.toLinearMap zero_lt_one).mpr
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have ht : TotallyBounded (K '' closedBall 0 1) :=
    (hK.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  obtain ⟨t,htsub,htfin,hcover⟩ := Metric.finite_approx_of_totallyBounded ht
    (ε / C) (div_pos hε hC)
  choose x hxball hx using fun y : t => htsub y.property
  let : Finite t := htfin.to_subtype
  refine ⟨Set.range (fun y : t => J (x y)), Set.finite_range _, ?_⟩
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨y,hy,hyv⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem K hv))
  refine mem_iUnion₂.mpr ⟨J (x ⟨y,hy⟩),mem_range_self _,?_⟩
  rw [mem_ball,dist_eq_norm]
  change ‖J v - J (x ⟨y,hy⟩)‖ < ε
  rw [← J.map_sub]
  apply (h (v-x ⟨y,hy⟩)).trans_lt
  rw [map_sub,hx]
  have hh : ‖K v - y‖ < ε / C := by simpa only [Metric.mem_ball, dist_eq_norm] using hyv
  have := (lt_div_iff₀ hC).mp hh
  simpa only [mul_comm] using this
end StrictHotSpots
end CompactDominationCombinedLayer

section BoundedCompactEmbeddingCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
open DiskH10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) {R : ℝ} (hR : 1 ≤ R)
  (hb : Ω ⊆ Metric.ball 0 R)

def dilation : H10 hΩ →L[ℝ] H10 PlaneGreen.diskOpen :=
  ((smoothTestToH10 PlaneGreen.diskOpen).comp (dilateTest hR hb)).extendOfNorm (smoothTestToH10 hΩ)

lemma dilation_test (f : smoothTestSpace Ω) :
    dilation hΩ hR hb (smoothTestToH10 hΩ f) =
      smoothTestToH10 PlaneGreen.diskOpen (dilateTest hR hb f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 hΩ)
    ⟨1,fun f => by
      rw [one_mul]
      exact dilateTest_norm hΩ hR hb f⟩ f

lemma dilation_value_sq (u : H10 hΩ) :
    ‖value PlaneGreen.diskOpen (dilation hΩ hR hb u)‖^2 =
      (R^2)⁻¹ * ‖value hΩ u‖^2 := by
  apply isClosed_property (dense_smoothTestToH10 hΩ) _ _ u
  · exact isClosed_eq (((value PlaneGreen.diskOpen).continuous.comp
      (dilation hΩ hR hb).continuous).norm.pow 2)
      (continuous_const.mul ((value hΩ).continuous.norm.pow 2))
  · intro f
    rw [dilation_test]
    exact dilateTest_value_sq hΩ hR hb f

private lemma le_mul_of_inv_sq {a b R : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : 0 < R) (h : b^2 = (R^2)⁻¹ * a^2) : a ≤ R * b := by
  have he : R^2 * b^2 = a^2 := by rw [h]; field_simp
  nlinarith [mul_nonneg hR.le hb]

lemma value_dilation_bound (u : H10 hΩ) :
    ‖value hΩ u‖ ≤ R * ‖value PlaneGreen.diskOpen (dilation hΩ hR hb u)‖ :=
  le_mul_of_inv_sq (norm_nonneg _) (norm_nonneg _) (zero_lt_one.trans_le hR)
    (dilation_value_sq hΩ hR hb u)

include hR hb in
lemma value_compact_of_ball : IsCompactOperator (value hΩ) := by
  let K : H10 hΩ →L[ℝ] Lp ℝ 2 (volume.restrict disk) :=
    (value PlaneGreen.diskOpen).comp (dilation hΩ hR hb)
  have hK : IsCompactOperator K := PlaneGreen.value_compact.comp_clm (dilation hΩ hR hb)
  exact compact_of_norm_dominated (value hΩ) K hK (zero_lt_one.trans_le hR)
    (value_dilation_bound hΩ hR hb)

include hΩ in
lemma value_compact (hbounded : Bornology.IsBounded Ω) : IsCompactOperator (value hΩ) := by
  obtain ⟨r,hr⟩ := hbounded.subset_ball (0 : Plane)
  exact value_compact_of_ball hΩ (le_max_left 1 r)
    (hr.trans (Metric.ball_subset_ball (le_max_right 1 r)))

end StrictHotSpots.H10
end BoundedCompactEmbeddingCombinedLayer

section PositiveCompactCombinedLayer
open Set
open scoped InnerProductSpace
namespace StrictHotSpots

lemma positive_norm_mem_spectrum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℝ] H) (hs : T.IsSymmetric) (hp : ∀ x, 0 ≤ inner ℝ (T x) x) :
    ‖T‖ ∈ spectrum ℝ T := by
  by_contra h
  have hr : algebraMap ℝ ℝ ‖T‖ ∈ resolventSet ℝ T := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (not_not.mp h)
  obtain ⟨ε,hε,hgap⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hr
  have hn := T.norm_eq_iSup_rayleighQuotient hs
  have hbound : ‖T‖ ≤ ‖T‖ - ε := by
    calc
      ‖T‖ = ⨆ x, |T.rayleighQuotient x| := hn
      _ ≤ ‖T‖ - ε := by
        apply ciSup_le
        intro x
        have hx : 0 ≤ T.rayleighQuotient x := by
          exact div_nonneg (hp x) (sq_nonneg _)
        rw [abs_of_nonneg hx]
        exact hgap x
  linarith

lemma positive_compact_top_eigenvector {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hs : T.IsSymmetric) (hp : ∀ x, 0 ≤ inner ℝ (T x) x)
    (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ f : H, f ≠ 0 ∧ T f = ‖T‖ • f := by
  have : Nontrivial H := not_subsingleton_iff_nontrivial.mp (by
    intro hh
    apply hne
    ext x
    exact Subsingleton.elim _ _)
  have he := (hc.hasEigenvalue_iff_mem_spectrum (norm_ne_zero_iff.mpr hne)).mpr
    (positive_norm_mem_spectrum T hs hp)
  obtain ⟨f,hf⟩ := he.exists_hasEigenvector
  exact ⟨f,hf.2,Module.End.mem_eigenspace_iff.mp hf.1⟩

end StrictHotSpots
end PositiveCompactCombinedLayer

section DirichletAttainmentCombinedLayer
open Set
open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] in
lemma energy_nonneg (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (v : V) :
    0 ≤ B v v := by
  obtain ⟨C,hC,h⟩ := hB
  exact (mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (norm_nonneg _)).trans (h v)

omit [CompleteSpace V] in
lemma energy_eq_zero (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) {v : V}
    (h : B v v = 0) : v = 0 := by
  obtain ⟨C,hC,hc⟩ := hB
  have hh := hc v
  rw [h] at hh
  have : ‖v‖ = 0 := le_antisymm (le_of_not_gt (fun hv =>
    (not_lt_of_ge hh) (mul_pos (mul_pos hC hv) hv))) (norm_nonneg v)
  exact norm_eq_zero.mp this

lemma green_ne_zero (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (hJ : J ≠ 0) : green B hB J ≠ 0 := by
  intro h
  apply hJ
  ext v
  have hS : solution B hB J (J v) = 0 := by
    apply energy_eq_zero B hB
    rw [solution_spec, ← green_apply, h, zero_apply, inner_zero_right]
  have ht := solution_spec B hB J (J v) v
  rw [hS, map_zero, zero_apply, real_inner_self_eq_norm_sq] at ht
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (J v)])



lemma minimum_attained (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsym : ∀ u v, B u v = B v u) (J : V →L[ℝ] H)
    (hJ : J ≠ 0) (hc : IsCompactOperator J) :
    ∃ (lam : ℝ) (φ : V), 0 < lam ∧ J φ ≠ 0 ∧
      (∀ v, lam * ‖J v‖^2 ≤ B v v) ∧
      (∀ v, B φ v = lam * inner ℝ (J φ) (J v)) := by
  let T := green B hB J
  have hT : T ≠ 0 := green_ne_zero B hB J hJ
  have hθ : 0 < ‖T‖ := norm_pos_iff.mpr hT
  obtain ⟨f,hf,he⟩ := positive_compact_top_eigenvector T
    (green_symmetric B hB hsym J) (fun f => by
      rw [real_inner_comm]; exact green_nonneg B hB J f)
    (hc.comp_clm (solution B hB J)) hT
  let φ := solution B hB J f
  have hφ : J φ = ‖T‖ • f := he
  refine ⟨‖T‖⁻¹,φ,inv_pos.mpr hθ,?_,?_,?_⟩
  · rw [hφ]
    exact smul_ne_zero hθ.ne' hf
  · intro v
    let w := solution B hB J (J v)
    have hw : B w v = ‖J v‖^2 := by
      rw [solution_spec, real_inner_self_eq_norm_sq]
    have hw' : B v w = ‖J v‖^2 := (hsym v w).trans hw
    have hww : B w w ≤ ‖T‖ * ‖J v‖^2 := by
      calc
        _ = inner ℝ (J v) (T (J v)) := solution_spec B hB J (J v) w
        _ ≤ ‖J v‖ * ‖T (J v)‖ := real_inner_le_norm _ _
        _ ≤ ‖J v‖ * (‖T‖ * ‖J v‖) := by
          gcongr; exact T.le_opNorm _
        _ = _ := by ring
    have hpos := energy_nonneg B hB (‖T‖ • v - w)
    simp only [map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul] at hpos
    rw [hw,hw'] at hpos
    have hineq : ‖J v‖^2 ≤ ‖T‖ * B v v := by nlinarith
    rw [inv_mul_eq_div, div_le_iff₀ hθ]
    nlinarith
  · intro v
    rw [solution_spec, hφ, real_inner_smul_left]
    field_simp

end StrictHotSpots.DirichletOperator
end DirichletAttainmentCombinedLayer

section DirichletMinimumCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)
local instance : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace

lemma value_ne_zero (hne : Ω.Nonempty) : value hΩ ≠ 0 := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨f,hs,hc,hf,_,hfa⟩ := exists_contDiff_tsupport_subset (n := ⊤) (hΩ.mem_nhds ha)
  let t : smoothTestSpace Ω := ⟨f,hf,hc,hs⟩
  intro hz
  have he : (test_memLp (Ω := Ω) hf hc).toLp f = 0 := by
    change value hΩ (smoothTestToH10 hΩ t) = 0
    exact DFunLike.congr_fun hz (smoothTestToH10 hΩ t)
  have hae : f =ᵐ[volume.restrict Ω] (fun _ => (0 : ℝ)) :=
    (test_memLp hf hc).coeFn_toLp.symm.trans (he ▸ Lp.coeFn_zero _ _ _)
  have hp := Measure.eqOn_open_of_ae_eq hae hΩ hf.continuous.continuousOn continuousOn_const ha
  exact zero_ne_one (hp.symm.trans hfa)



lemma minimum (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ (lam : ℝ) (φ : H10 hΩ), 0 < lam ∧ value hΩ φ ≠ 0 ∧
      (∀ v, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2) ∧
      (∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
        lam * inner ℝ (value hΩ φ) (value hΩ v)) := by
  have hsym : ∀ u v : H10 hΩ, energy hΩ u v = energy hΩ v u := by
    intro u v
    exact (real_inner_comm (grad hΩ u) (grad hΩ v)).symm
  have hm := @DirichletOperator.minimum_attained (H10 hΩ) (Lp ℝ 2 (volume.restrict Ω))
    (H10.normedAddCommGroup hΩ) (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    inferInstance inferInstance inferInstance (energy hΩ) (energy_coercive hΩ hb)
    hsym (value hΩ) (value_ne_zero hΩ hne) (value_compact hΩ hb)
  obtain ⟨lam,φ,hl,hφ,hineq,heq⟩ := hm
  refine ⟨lam,φ,hl,hφ,?_,heq⟩
  intro v
  simpa only [energy_apply,real_inner_self_eq_norm_sq] using hineq v

end StrictHotSpots.H10
end DirichletMinimumCombinedLayer

section StrictGapAlgebraCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots
namespace H1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace

def corrected (φ v : H1 Ω) : H1 Ω := v - ((mean hb v) / (mean hb φ)) • φ
lemma mean_corrected (φ v : H1 Ω) (hφ : mean hb φ ≠ 0) :
    mean hb (corrected hb φ v) = 0 := by
  simp only [corrected,map_sub,map_smul,smul_eq_mul]
  field_simp
  ring
lemma corrected_form (lam : ℝ) (φ v : H1 Ω) (hφ : form lam φ φ = 0)
    (hv : form lam v φ = 0) : form lam (corrected hb φ v) (corrected hb φ v) = form lam v v :=
  form_diag_sub _ _ _ _ hφ hv
end H1
namespace PlaneWaves
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace

lemma all_pair_zero {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hvol : 0 < (volume Ω).toReal) (φ : H10 hΩ)
    (he : H1.form lam φ.val φ.val = 0) (hm : H1.mean hb φ.val ≠ 0)
    {k : Plane} (hk : ‖k‖^2 = lam) {l : Plane} (hl : ‖l‖^2 = lam) :
    H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb l) = 0 ∧
      H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb l) = 0 := by
  let c := H1.corrected hb φ.val (cosH1 hΩ hb k)
  let s := H1.corrected hb φ.val (sinH1 hΩ hb k)
  have hmc : H1.mean hb c = 0 := H1.mean_corrected hb _ _ hm
  have hms : H1.mean hb s = 0 := H1.mean_corrected hb _ _ hm
  have hc : H1.form lam c c = H1.form lam (cosH1 hΩ hb k) (cosH1 hΩ hb k) :=
    H1.corrected_form hb _ _ _ he (cosH1_dirichlet_pair hΩ hb hk φ)
  have hs : H1.form lam s s = H1.form lam (sinH1 hΩ hb k) (sinH1 hΩ hb k) :=
    H1.corrected_form hb _ _ _ he (sinH1_dirichlet_pair hΩ hb hk φ)
  have hsum := self_sum hΩ hb hk
  have hcn := H1.form_nonneg hb hle c hmc
  have hsn := H1.form_nonneg hb hle s hms
  have hcz : H1.form lam c c = 0 := by linarith
  have hsz : H1.form lam s s = 0 := by linarith
  have hce := H1.form_zero_euler hb hle hvol c hmc hcz (cosH1 hΩ hb l)
  have hse := H1.form_zero_euler hb hle hvol s hms hsz (sinH1 hΩ hb l)
  have hcl : H1.form lam φ.val (cosH1 hΩ hb l) = 0 := by
    rw [H1.form_symm]; exact cosH1_dirichlet_pair hΩ hb hl φ
  have hsl : H1.form lam φ.val (sinH1 hΩ hb l) = 0 := by
    rw [H1.form_symm]; exact sinH1_dirichlet_pair hΩ hb hl φ
  simp only [c,s,H1.corrected,H1.form_sub_left,H1.form_smul_left,hcl,hsl,mul_zero,sub_zero]
    at hce hse
  exact ⟨hce,hse⟩
end PlaneWaves
end StrictHotSpots
end StrictGapAlgebraCombinedLayer

section NearbyFrequenciesCombinedLayer
open Set MeasureTheory Filter Metric
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots.PlaneWaves

def frequency (r θ : ℝ) : Plane := WithLp.toLp 2 ![r * Real.cos θ, r * Real.sin θ]
lemma frequency_norm_sq (r θ : ℝ) : ‖frequency r θ‖^2 = r^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [frequency,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]
lemma frequency_inner (r θ : ℝ) : inner ℝ (frequency r 0) (frequency r θ) = r^2 * Real.cos θ := by
  simp [frequency,PiLp.inner_apply,Fin.sum_univ_two,RCLike.inner_apply,pow_two]
  ring
lemma frequency_continuous (r : ℝ) : Continuous (frequency r) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi_iff.mpr
  intro i
  fin_cases i <;> fun_prop

lemma cosine_integral_continuous {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    Continuous (fun k : Plane => ∫ x in Ω, cosine k x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro k
    exact (cosine_smooth k).continuous.aestronglyMeasurable
  · intro k
    exact Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_cos_le_one _
  · exact integrable_const _
  · exact Eventually.of_forall fun x => Real.continuous_cos.comp (continuous_id.inner continuous_const)



lemma exists_nearby {Ω : Set Plane} (hb : Bornology.IsBounded Ω)
    (hvol : 0 < (volume Ω).toReal) {lam : ℝ} (hlam : 0 < lam) :
    ∃ k l : Plane, ‖k‖^2 = lam ∧ ‖l‖^2 = lam ∧ inner ℝ k l ≠ lam ∧
      0 < ∫ x in Ω, cosine (k-l) x := by
  let r := Real.sqrt lam
  have hr : r^2 = lam := Real.sq_sqrt hlam.le
  have hc : Continuous (fun θ : ℝ => ∫ x in Ω, cosine (frequency r 0 - frequency r θ) x) :=
    (cosine_integral_continuous hb).comp (continuous_const.sub (frequency_continuous r))
  have h0 : 0 < ∫ x in Ω, cosine (frequency r 0 - frequency r 0) x := by
    simpa [cosine,Measure.real] using hvol
  have he : ∀ᶠ θ in 𝓝 (0 : ℝ), 0 < ∫ x in Ω, cosine (frequency r 0 - frequency r θ) x :=
    hc.continuousAt.eventually (Ioi_mem_nhds h0)
  obtain ⟨δ,hδ,hδ'⟩ := Metric.eventually_nhds_iff.mp he
  let θ := min δ (Real.pi) / 2
  have ht : 0 < θ := by dsimp [θ]; positivity
  have htd : θ < δ := by dsimp [θ]; linarith [min_le_left δ Real.pi]
  have htp : θ < Real.pi := by dsimp [θ]; linarith [min_le_right δ Real.pi,Real.pi_pos]
  refine ⟨frequency r 0,frequency r θ,(frequency_norm_sq _ _).trans hr,
    (frequency_norm_sq _ _).trans hr,?_,hδ' (by simpa [Real.dist_eq,abs_of_pos ht] using htd)⟩
  rw [frequency_inner,hr]
  intro hx
  have hc1 : Real.cos θ = 1 := by nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi ht htp
  nlinarith [Real.sin_sq_add_cos_sq θ]
end StrictHotSpots.PlaneWaves
end NearbyFrequenciesCombinedLayer

section StrictGapCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace StrictHotSpots
namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

lemma zero_of_form_neumann (hb : Bornology.IsBounded Ω) (lam : ℝ) (φ : H10 hΩ)
    (he : ∀ v : H1 Ω, H1.form lam φ.val v = 0) : value hΩ φ = 0 := by
  apply zero_of_neumann hΩ hb lam φ
  intro v k hv
  have hh := he hv.toH1
  unfold H1.form at hh
  rw [H1.grad_toH1,H1.value_toH1,L2Inner.toLp_right,L2Inner.toLp_right] at hh
  have hf : (∫ x in Ω, inner ℝ (H1.value φ.val x) (v x)) =
      (∫ x in Ω, value hΩ φ x * v x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply,RCLike.conj_to_real]
      exact mul_comm _ _
  rw [hf,sub_eq_zero] at hh
  exact hh




lemma strict_gap (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    {lam : ℝ} (hlam : 0 < lam) (φ : H10 hΩ) (hφ : value hΩ φ ≠ 0)
    (he : ∀ v, inner ℝ (grad hΩ φ) (grad hΩ v) =
      lam * inner ℝ (value hΩ φ) (value hΩ v)) :
    firstPositiveNeumannValue Ω < lam := by
  by_contra hn
  have hle : lam ≤ firstPositiveNeumannValue Ω := le_of_not_gt hn
  have hvol : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (hΩ.measure_pos volume hne).ne' hb.measure_lt_top.ne
  have hform : H1.form lam φ.val φ.val = 0 := sub_eq_zero.mpr (he φ)
  have hm : H1.mean hb φ.val ≠ 0 := by
    intro hz
    apply hφ
    apply zero_of_form_neumann hΩ hb lam φ
    exact H1.form_zero_euler hb hle hvol φ.val hz hform
  obtain ⟨k,l,hk,hl,hkl,hint⟩ := PlaneWaves.exists_nearby hb hvol hlam
  obtain ⟨hc,hs⟩ := PlaneWaves.all_pair_zero hΩ hb hle hvol φ hform hm hk hl
  have hsum := PlaneWaves.pair_sum hΩ hb lam k l
  rw [hc,hs,zero_add] at hsum
  have hp : (inner ℝ k l - lam) * (∫ x in Ω, PlaneWaves.cosine (k-l) x) = 0 := hsum.symm
  exact hkl (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hint.ne'))

lemma subcritical (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    ∃ lam : ℝ, 0 < lam ∧ firstPositiveNeumannValue Ω < lam ∧
      ∀ v : H10 hΩ, lam * ‖value hΩ v‖^2 ≤ ‖grad hΩ v‖^2 := by
  obtain ⟨lam,φ,hl,hφ,hi,he⟩ := minimum hΩ hne hb
  exact ⟨lam,hl,strict_gap hΩ hne hb hl φ hφ he,hi⟩
end H10
end StrictHotSpots
end StrictGapCombinedLayer


end

end DouglasLipschitzBase

end OAI
