import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVPlanarLocalModels

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_coordinates_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : normalPlaneEmbedding n (normalPlaneCoordinates n x) = x := by
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart 0 n).surjective x
  have ht : t = 0 := by
    have hh := normalColumnChart_height 0 hn t y
    simp only [sub_zero] at hh
    exact hh.symm.trans hx
  rw [ht,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add,
    normalPlaneCoordinates_embedding]

lemma normalPlaneCoordinates_norm_of_inner_zero {n x : Cover} (hn : ‖n‖ = 1)
    (hx : ⟪n,x⟫ = 0) : ‖normalPlaneCoordinates n x‖ = ‖x‖ := by
  rw [← normalPlaneEmbedding_norm n,normalPlaneEmbedding_coordinates_of_inner_zero hn hx]

theorem integral_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0) (f : Cover → ℝ) :
    (∫ y : Plane, f (normalPlaneEmbedding n y)) = ∫ y : Plane, f (T y) := by
  let R : Plane →ₗᵢ[ℝ] Plane :=
    { toLinearMap := (normalPlaneCoordinates n).toLinearMap.comp T.toLinearMap
      norm_map' := fun y ↦ (normalPlaneCoordinates_norm_of_inner_zero hn (hT y)).trans (T.norm_map y) }
  have hR : Function.Surjective R :=
    (LinearMap.injective_iff_surjective (f := R.toLinearMap)).mp R.injective
  let e := LinearIsometryEquiv.ofSurjective R hR
  have he (y : Plane) : normalPlaneEmbedding n (e y) = T y :=
    normalPlaneEmbedding_coordinates_of_inner_zero hn (hT y)
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  simp_rw [he]

lemma radial_face_coefficients (u : ℝ) :
    (u/Real.sqrt (1+u^2))^2+(1/Real.sqrt (1+u^2))^2 = 1 := by
  have hpos : (0 : ℝ) < 1+u^2 := by positivity
  have hs := Real.sq_sqrt hpos.le
  have hd := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  nlinarith

def radialFaceNormal (u : ℝ) : Cover :=
  WithLp.toLp 2 ![0,1/Real.sqrt (1+u^2),-u/Real.sqrt (1+u^2)]

lemma radialFaceNormal_norm (u : ℝ) : ‖radialFaceNormal u‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  have hh := radial_face_coefficients u
  simpa [radialFaceNormal,neg_div,neg_sq,add_comm] using hh

def radialFaceIsometry (u : ℝ) : Plane →ₗᵢ[ℝ] Cover where
  toFun y := WithLp.toLp 2 ![y 0,(u/Real.sqrt (1+u^2))*(y 1),(1/Real.sqrt (1+u^2))*(y 1)]
  map_add' y z := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' t y := by ext i; fin_cases i <;> simp [mul_left_comm]
  norm_map' y := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,Fin.sum_univ_two]
    change (y 0)^2+((u/Real.sqrt (1+u^2))*(y 1))^2+((1/Real.sqrt (1+u^2))*(y 1))^2 = (y 0)^2+(y 1)^2
    calc
      _ = (y 0)^2+((u/Real.sqrt (1+u^2))^2+(1/Real.sqrt (1+u^2))^2)*(y 1)^2 := by ring
      _ = _ := by rw [radial_face_coefficients,one_mul]

lemma radialFaceIsometry_perp (u : ℝ) (y : Plane) :
    ⟪radialFaceNormal u,radialFaceIsometry u y⟫ = 0 := by
  simp [radialFaceNormal,radialFaceIsometry,EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct,Fin.sum_univ_three]
  ring

theorem integral_radialFace (u : ℝ) (f : Cover → ℝ) :
    (∫ y : Plane, f (normalPlaneEmbedding (radialFaceNormal u) y)) =
      ∫ y : Plane, f (radialFaceIsometry u y) :=
  integral_normalPlane_eq_isometry (radialFaceNormal_norm u) (radialFaceIsometry u)
    (radialFaceIsometry_perp u) f

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {ι : Type*} [Fintype ι]

def strictPatchOpen (g : ι → Cover → ℝ) : Set Cover := {x | ∀ i, 0 < g i x}
def strictPatchClosed (g : ι → Cover → ℝ) : Set Cover := {x | ∀ i, 0 ≤ g i x}
def strictPatchCutoff (g : ι → Cover → ℝ) (ε : ℝ) (x : Cover) : ℝ :=
  ∏ i, Real.smoothTransition (g i x/ε-1)

lemma strictPatchCutoff_contDiff {g : ι → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (strictPatchCutoff g ε) :=
  contDiff_prod (fun i _ ↦ Real.smoothTransition.contDiff.comp
    (((hg i).div_const ε).sub contDiff_const))

lemma strictPatchCutoff_bounds (g : ι → Cover → ℝ) (ε : ℝ) (x : Cover) :
    strictPatchCutoff g ε x ∈ Icc 0 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ ↦ Real.smoothTransition.nonneg _)
  · exact Finset.prod_le_one₀ (fun i _ ↦ Real.smoothTransition.nonneg _)
      (fun i _ ↦ Real.smoothTransition.le_one _)

lemma strictPatchCutoff_support {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    {ε : ℝ} (hε : 0 < ε) : tsupport (strictPatchCutoff g ε) ⊆ {x | ∀ i, ε ≤ g i x} := by
  classical
  apply closure_minimal
  · intro x hx i
    by_contra hh
    have hz : Real.smoothTransition (g i x/ε-1) = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      have hh' : g i x ≤ ε := le_of_not_ge hh
      have hd := (div_le_one hε).mpr hh'
      linarith
    apply hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  · have he : {x : Cover | ∀ i, ε ≤ g i x} = ⋂ i, {x | ε ≤ g i x} := by ext; simp
    rw [he]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const (hg i))

lemma strictPatchCutoff_tsupport_open {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    {ε : ℝ} (hε : 0 < ε) : tsupport (strictPatchCutoff g ε) ⊆ strictPatchOpen g := by
  intro x hx i
  exact hε.trans_le (strictPatchCutoff_support hg hε hx i)

omit [Fintype ι] in
lemma strictPatchOpen_subset_closed (g : ι → Cover → ℝ) :
    strictPatchOpen g ⊆ strictPatchClosed g := fun _ hx i ↦ (hx i).le

lemma strictPatchCutoff_hasCompactSupport {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i))
    (hK : IsCompact (strictPatchClosed g)) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (strictPatchCutoff g ε) :=
  hK.of_isClosed_subset isClosed_closure
    ((strictPatchCutoff_tsupport_open hg hε).trans (strictPatchOpen_subset_closed g))

lemma measurableSet_strictPatchOpen {g : ι → Cover → ℝ} (hg : ∀ i, Continuous (g i)) :
    MeasurableSet (strictPatchOpen g) := by
  have he : strictPatchOpen g = ⋂ i, {x | 0 < g i x} := by ext; simp [strictPatchOpen]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const (hg i).measurable)

lemma strictPatchCutoff_tendsto (g : ι → Cover → ℝ)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) (x : Cover) :
    Tendsto (fun j ↦ strictPatchCutoff g (ε j) x) atTop
      (𝓝 ((strictPatchOpen g).indicator (fun _ ↦ (1 : ℝ)) x)) := by
  classical
  by_cases hx : x ∈ strictPatchOpen g
  · rw [indicator_of_mem hx]
    have he (i : ι) : ∀ᶠ j in atTop, Real.smoothTransition (g i x/ε j-1) = 1 := by
      filter_upwards [hlim.eventually (gt_mem_nhds (half_pos (hx i)))] with j hj
      apply Real.smoothTransition.one_of_one_le
      have hh := (le_div_iff₀ (hε j)).mpr (show (2 : ℝ)*ε j ≤ g i x by linarith)
      linarith
    have hall : ∀ᶠ j in atTop, ∀ i, Real.smoothTransition (g i x/ε j-1) = 1 :=
      eventually_all.mpr he
    apply tendsto_const_nhds.congr'
    filter_upwards [hall] with j hj
    simp only [strictPatchCutoff,hj,Finset.prod_const_one]
  · rw [indicator_of_notMem hx]
    simp only [strictPatchOpen,mem_ofPred_eq,not_forall,not_lt] at hx
    obtain ⟨i,hi⟩ := hx
    have hz (j : ℕ) : strictPatchCutoff g (ε j) x = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Real.smoothTransition.zero_of_nonpos
      have hh := div_nonpos_of_nonpos_of_nonneg hi (hε j).le
      linarith
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma blowup_weighted_remainder_le {ν : FiniteMeasure BlowupNormalBundle} {O : Set Cover}
    {w : BlowupNormalBundle → ℝ}
    (hiw : Integrable w ((ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}))
    (hwb : ∀ z, w z ∈ Icc 0 1)
    {F : Cover → Cover} (hF : Continuous F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) -
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) ≤
    (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ O} -
      (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, w z ∂(ν : Measure BlowupNormalBundle)) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let T : BlowupNormalBundle → ℝ := fun z ↦ ⟪(z.2 : Cover),F z.1⟫
  have hTc : Continuous T := (continuous_subtype_val.comp continuous_snd).inner (hF.comp continuous_fst)
  have hTb (z : BlowupNormalBundle) : |T z| ≤ 1 := blowup_test_inner_bound hnF z
  have hiT : Integrable T μ := Integrable.of_bound hTc.aestronglyMeasurable 1 (ae_of_all μ hTb)
  have hiwT : Integrable (fun z ↦ w z*T z) μ := by
    simpa only [mul_comm] using hiw.bdd_mul hTc.aestronglyMeasurable (ae_of_all μ hTb)
  have hm := integral_mono (hiT.sub hiwT) ((integrable_const (1 : ℝ)).sub hiw) (fun z ↦ show
      T z-w z*T z ≤ 1-w z from by
        have ht := (le_abs_self (T z)).trans (hTb z)
        nlinarith [mul_nonneg (sub_nonneg.mpr (hwb z).2) (sub_nonneg.mpr ht)])
  simp only [Pi.sub_apply] at hm
  rw [integral_sub hiT hiwT,integral_sub (integrable_const 1) hiw,integral_const] at hm
  simpa only [μ,T,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hm

theorem blowup_two_flat_patches_remainder_le {A O U₁ U₂ : Set Cover} (hA : MeasurableSet A)
    {n₁ n₂ : Cover} (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hflat₁ : ∀ᵐ x : Cover ∂volume, x ∈ U₁ → (x ∈ A ↔ x ∈ coverHalfspace n₁))
    (hflat₂ : ∀ᵐ x : Cover ∂volume, x ∈ U₂ → (x ∈ A ↔ x ∈ coverHalfspace n₂))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ₁ φ₂ : Cover → ℝ}
    (hφ₁ : ContDiff ℝ (⊤ : ℕ∞) φ₁) (hs₁ : HasCompactSupport φ₁)
    (hφ₂ : ContDiff ℝ (⊤ : ℕ∞) φ₂) (hs₂ : HasCompactSupport φ₂)
    (hU₁ : tsupport φ₁ ⊆ U₁) (hU₂ : tsupport φ₂ ⊆ U₂)
    (hO₁ : tsupport φ₁ ⊆ O) (hO₂ : tsupport φ₂ ⊆ O)
    (hb₁ : ∀ x, φ₁ x ∈ Icc 0 1) (hb₂ : ∀ x, φ₂ x ∈ Icc 0 1)
    (hsum : ∀ x, φ₁ x+φ₂ x ≤ 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      (∫ y : Plane, φ₁ (normalPlaneEmbedding n₁ y)*⟪n₁,F (normalPlaneEmbedding n₁ y)⟫) -
      (∫ y : Plane, φ₂ (normalPlaneEmbedding n₂ y)*⟪n₂,F (normalPlaneEmbedding n₂ y)⟫) ≤
    (coverLocalPerimeter A O).toReal -
      (∫ y : Plane, φ₁ (normalPlaneEmbedding n₁ y)) -
      (∫ y : Plane, φ₂ (normalPlaneEmbedding n₂ y)) := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ {φ : Cover → ℝ} (hc : Continuous φ) (hb : ∀ x, φ x ∈ Icc 0 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hc.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb z.1).1]; exact (hb z.1).2)
  have hi₁ := hiφ hφ₁.continuous hb₁
  have hi₂ := hiφ hφ₂.continuous hb₂
  have hiF {φ : Cover → ℝ} (hi : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm,Function.comp_apply] using hi.bdd_mul
      ((continuous_subtype_val.comp continuous_snd).inner
        (hF.continuous.comp continuous_fst)).aestronglyMeasurable
      (ae_of_all μ (blowup_test_inner_bound hnF))
  have hh := blowup_weighted_remainder_le (hi₁.add hi₂)
    (fun z ↦ ⟨add_nonneg (hb₁ z.1).1 (hb₂ z.1).1,hsum z.1⟩) hF.continuous hnF
  simp only [Pi.add_apply,add_mul] at hh
  rw [integral_add (hiF hi₁) (hiF hi₂),integral_add hi₁ hi₂] at hh
  have htot : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hflux F hF hs hO hnF
    intro z hz
    have he : F z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hO h))
    simp only [he,inner_zero_right]
  rw [htot,blowup_flat_patch_weighted_flux hA hn₁ hflat₁ hflux hφ₁ hs₁ hU₁ hO₁ hb₁ hF hnF,
    blowup_flat_patch_weighted_flux hA hn₂ hflat₂ hflux hφ₂ hs₂ hU₂ hO₂ hb₂ hF hnF,
    blowup_flat_patch_weighted_mass hA hn₁ hflat₁ heq hflux hφ₁ hs₁ hU₁ hO₁ hb₁,
    blowup_flat_patch_weighted_mass hA hn₂ hflat₂ heq hflux hφ₂ hs₂ hU₂ hO₂ hb₂] at hh
  rw [Measure.real,← heq] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {ι : Type*} [Fintype ι]

theorem strictPatchCutoff_integral_tendsto {g : ι → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (hK : IsCompact (strictPatchClosed g))
    (T : Plane →ₗᵢ[ℝ] Cover) {f : Cover → ℝ} (hf : Continuous f) (hfb : ∀ x, |f x| ≤ 1)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y : Plane, strictPatchCutoff g (ε i) (T y)*f (T y)) atTop
      (𝓝 (∫ y in T ⁻¹' strictPatchOpen g, f (T y))) := by
  let K : Set Plane := T ⁻¹' strictPatchClosed g
  have hKc : IsCompact K := T.isometry.isClosedEmbedding.isCompact_preimage hK
  have hi : Integrable (K.indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKc.measurableSet
  have hb (i : ℕ) (y : Plane) :
      ‖strictPatchCutoff g (ε i) (T y)*f (T y)‖ ≤ K.indicator (fun _ ↦ (1 : ℝ)) y := by
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy,norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (strictPatchCutoff_bounds g (ε i) (T y)).1,Real.norm_eq_abs]
      exact (mul_le_mul (strictPatchCutoff_bounds g (ε i) (T y)).2 (hfb (T y))
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · rw [indicator_of_notMem hy]
      have hz : strictPatchCutoff g (ε i) (T y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hh
        exact hy (strictPatchOpen_subset_closed g
          (strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i) hh))
      simp only [hz,zero_mul,norm_zero,le_refl]
  have ht := tendsto_integral_of_dominated_convergence (K.indicator (fun _ ↦ (1 : ℝ)))
    (fun i ↦ (((strictPatchCutoff_contDiff hg (ε i)).continuous.comp T.continuous).mul
      (hf.comp T.continuous)).aestronglyMeasurable)
    hi (fun i ↦ ae_of_all volume (hb i))
    (ae_of_all volume (fun y ↦ (strictPatchCutoff_tendsto g hε hlim (T y)).mul_const (f (T y))))
  have he : (fun y : Plane ↦ (strictPatchOpen g).indicator (fun _ ↦ (1 : ℝ)) (T y)*f (T y)) =
      (T ⁻¹' strictPatchOpen g).indicator (fun y ↦ f (T y)) := by
    funext y
    by_cases hy : T y ∈ strictPatchOpen g <;> simp [hy]
  rw [he,integral_indicator ((measurableSet_strictPatchOpen (fun i ↦ (hg i).continuous)).preimage T.continuous.measurable)] at ht
  exact ht

lemma strictPatchCutoff_disjoint_sum_le_one {κ : Type*} [Fintype κ]
    {g : ι → Cover → ℝ} {h : κ → Cover → ℝ}
    (hg : ∀ i, Continuous (g i)) (hh : ∀ i, Continuous (h i))
    (hd : Disjoint (strictPatchOpen g) (strictPatchOpen h)) {ε : ℝ} (hε : 0 < ε)
    (x : Cover) : strictPatchCutoff g ε x+strictPatchCutoff h ε x ≤ 1 := by
  by_cases hx : x ∈ strictPatchOpen g
  · have hx' : x ∉ strictPatchOpen h := fun hxh ↦ Set.disjoint_left.mp hd hx hxh
    have hz : strictPatchCutoff h ε x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx' (strictPatchCutoff_tsupport_open hh hε h))
    rw [hz,add_zero]
    exact (strictPatchCutoff_bounds _ _ _).2
  · have hz : strictPatchCutoff g ε x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (strictPatchCutoff_tsupport_open hg hε h))
    rw [hz,zero_add]
    exact (strictPatchCutoff_bounds _ _ _).2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem blowup_two_polytope_patches_remainder_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {g : ι → Cover → ℝ} {h : κ → Cover → ℝ}
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i))
    (hKg : IsCompact (strictPatchClosed g)) (hKh : IsCompact (strictPatchClosed h))
    (hdis : Disjoint (strictPatchOpen g) (strictPatchOpen h))
    {A O : Set Cover} (hA : MeasurableSet A)
    {n₁ n₂ : Cover} (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (hflat₁ : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen g → (x ∈ A ↔ x ∈ coverHalfspace n₁))
    (hflat₂ : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen h → (x ∈ A ↔ x ∈ coverHalfspace n₂))
    (hgO : strictPatchOpen g ⊆ O) (hhO : strictPatchOpen h ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      (∫ y in normalPlaneEmbedding n₁ ⁻¹' strictPatchOpen g, ⟪n₁,F (normalPlaneEmbedding n₁ y)⟫) -
      (∫ y in normalPlaneEmbedding n₂ ⁻¹' strictPatchOpen h, ⟪n₂,F (normalPlaneEmbedding n₂ y)⟫) ≤
    (coverLocalPerimeter A O).toReal -
      volume.real (normalPlaneEmbedding n₁ ⁻¹' strictPatchOpen g) -
      volume.real (normalPlaneEmbedding n₂ ⁻¹' strictPatchOpen h) := by
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ)+1)
  have hε (i : ℕ) : 0 < ε i := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht₁ := strictPatchCutoff_integral_tendsto hg hKg (normalPlaneLinearIsometry n₁)
    (continuous_const.inner hF.continuous)
    (fun x ↦ (abs_real_inner_le_norm n₁ (F x)).trans (by rw [hn₁,one_mul]; exact hnF x)) hε hlim
  have ht₂ := strictPatchCutoff_integral_tendsto hh hKh (normalPlaneLinearIsometry n₂)
    (continuous_const.inner hF.continuous)
    (fun x ↦ (abs_real_inner_le_norm n₂ (F x)).trans (by rw [hn₂,one_mul]; exact hnF x)) hε hlim
  have hm₁ := strictPatchCutoff_integral_tendsto hg hKg (normalPlaneLinearIsometry n₁)
    (continuous_const (y := (1 : ℝ))) (fun _ ↦ le_of_eq (abs_one)) hε hlim
  have hm₂ := strictPatchCutoff_integral_tendsto hh hKh (normalPlaneLinearIsometry n₂)
    (continuous_const (y := (1 : ℝ))) (fun _ ↦ le_of_eq (abs_one)) hε hlim
  simp only [mul_one,integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] at hm₁ hm₂
  apply le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub ht₁).sub ht₂)
    ((tendsto_const_nhds.sub hm₁).sub hm₂)
  exact Filter.Eventually.of_forall (fun i ↦ blowup_two_flat_patches_remainder_le hA hn₁ hn₂
    hflat₁ hflat₂ heq hflux
    (strictPatchCutoff_contDiff hg (ε i))
    (strictPatchCutoff_hasCompactSupport (fun j ↦ (hg j).continuous) hKg (hε i))
    (strictPatchCutoff_contDiff hh (ε i))
    (strictPatchCutoff_hasCompactSupport (fun j ↦ (hh j).continuous) hKh (hε i))
    (strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i))
    (strictPatchCutoff_tsupport_open (fun j ↦ (hh j).continuous) (hε i))
    ((strictPatchCutoff_tsupport_open (fun j ↦ (hg j).continuous) (hε i)).trans hgO)
    ((strictPatchCutoff_tsupport_open (fun j ↦ (hh j).continuous) (hε i)).trans hhO)
    (strictPatchCutoff_bounds g (ε i)) (strictPatchCutoff_bounds h (ε i))
    (strictPatchCutoff_disjoint_sum_le_one (fun j ↦ (hg j).continuous)
      (fun j ↦ (hh j).continuous) hdis (hε i)) hF hs hO hnF)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma abs_prismRadialFlux_le {X Y : PrismCoordinates → ℝ}
    (hn : ∀ z, (X z)^2+(Y z)^2 ≤ 1)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) :
    |prismRadialFlux X Y a c b l u| ≤
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
  have hface (t s : ℝ) :
      |(X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))| ≤
        Real.sqrt (1+l^2)+Real.sqrt (1+u^2) := by
    have hu := abs_planar_normal_flux (hn (t,(s*u,s))) u
    have hl := abs_planar_normal_flux (hn (t,(s*l,s))) l
    exact (abs_sub _ _).trans (by linarith)
  have hinner (t : ℝ) : |∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))| ≤
      b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := b) (fun s _ ↦ show
        ‖(X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))‖ ≤
          Real.sqrt (1+l^2)+Real.sqrt (1+u^2) by
        simpa only [Real.norm_eq_abs] using hface t s)
    simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg hb,mul_comm] using hi
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := c) (fun t _ ↦ show ‖∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))‖ ≤
      b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) by
      simpa only [Real.norm_eq_abs] using hinner t)
  simpa only [prismRadialFlux,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hac),
    mul_comm,mul_left_comm,mul_assoc] using hi

lemma cover_field_planar_sq_bound {v : Cover} (hv : ‖v‖ ≤ 1) : (v 1)^2+(v 2)^2 ≤ 1 := by
  have he := EuclideanSpace.real_norm_sq_eq v
  rw [Fin.sum_univ_three] at he
  nlinarith [sq_nonneg (v 0),norm_nonneg v]

lemma cover_field_component_bound {v : Cover} (hv : ‖v‖ ≤ 1) (i : Fin 3) : |v i| ≤ 1 := by
  have he : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  exact he.trans hv

theorem coverLocalPerimeter_euclideanPrism_le (O : Set Cover)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    coverLocalPerimeter (euclideanPrism a c b l u) O ≤ ENNReal.ofReal
      ((c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)+(u-l))+b^2*(u-l)) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro _
  apply iSup_le; intro hnorm
  apply ENNReal.ofReal_le_ofReal
  rw [integral_euclideanPrism_divergence hF hs hac hb hlu]
  have hr := abs_prismRadialFlux_le
    (fun z ↦ cover_field_planar_sq_bound (hnorm (coverPrismCoordinates.symm z)))
    (l := l) (u := u) hac hb
  have hc := abs_prismClosingFlux_le
    (fun z ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm z)) 0)
    (fun z ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm z)) 2) hac hb hlu
  have hs := (le_abs_self _).trans ((abs_add_le _ _).trans (add_le_add hr hc))
  nlinarith [hs]

theorem euclideanPrism_closing_error_bound {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) (hnorm : ∀ x, ‖F x‖ ≤ 1)
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u) :
    |(∫ x in euclideanPrism a c b l u, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u| ≤
      (c-a)*b*(u-l)+b^2*(u-l) := by
  rw [integral_euclideanPrism_divergence hF hs hac hb hlu,add_sub_cancel_left]
  exact abs_prismClosingFlux_le
    (fun z ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm z)) 0)
    (fun z ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm z)) 2) hac hb hlu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology symmDiff
namespace CubicTorus

theorem integral_prism_surgery {A : Set Cover}
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in A \ euclideanPrism a c b l u, divergence F x) =
      (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u -
      prismClosingFlux (fun w ↦ F (coverPrismCoordinates.symm w) 0)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u := by
  have hc : HasCompactSupport (divergence F) :=
    hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  have hi := (continuous_divergence hF).integrable_of_hasCompactSupport (μ := volume) hc
  have he : (A ∩ euclideanPrism a c b l u : Set Cover) =ᵐ[volume] euclideanPrism a c b l u := by
    filter_upwards [hPA] with x hx
    exact propext ⟨fun h ↦ h.2,fun h ↦ ⟨hx h,h⟩⟩
  have hh := integral_inter_add_sdiff (measurableSet_euclideanPrism a c b l u)
    (hi.integrableOn (s := A))
  rw [setIntegral_congr_set he,integral_euclideanPrism_divergence hF hs hac hb hlu] at hh
  linarith

theorem integral_prism_surgery_error {A : Set Cover}
    {a c b l u : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hnorm : ∀ x, ‖F x‖ ≤ 1) :
    |(∫ x in A \ euclideanPrism a c b l u, divergence F x) -
      ((∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u)| ≤
      (c-a)*b*(u-l)+b^2*(u-l) := by
  rw [integral_prism_surgery hac hb hlu hPA hF hs]
  simp only [sub_sub_cancel_left,abs_neg]
  exact abs_prismClosingFlux_le
    (fun w ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm w)) 0)
    (fun w ↦ cover_field_component_bound (hnorm (coverPrismCoordinates.symm w)) 2) hac hb hlu

theorem coverLocalPerimeter_prism_surgery_le {A O : Set Cover}
    {a c b l u M : ℝ} (hac : a ≤ c) (hb : 0 ≤ b) (hlu : l ≤ u)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hrem : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u ≤ M) :
    coverLocalPerimeter (A \ euclideanPrism a c b l u) O ≤
      ENNReal.ofReal (M+(c-a)*b*(u-l)+b^2*(u-l)) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro hO
  apply iSup_le; intro hn
  apply ENNReal.ofReal_le_ofReal
  have he := integral_prism_surgery_error hac hb hlu hPA hF hs hn
  have hh := hrem F hF hs hO hn
  have he' := (le_abs_self _).trans he
  linarith

lemma prism_surgery_symmDiff_subset (A : Set Cover) (a c b l u : ℝ) :
    A ∆ (A \ euclideanPrism a c b l u) ⊆ euclideanPrism a c b l u := by
  intro x hx
  simp only [mem_symmDiff,Set.mem_sdiff] at hx
  rcases hx with hx | hx
  · exact Classical.byContradiction (fun hh ↦ hx.2 ⟨hx.1,hh⟩)
  · exact False.elim (hx.2 hx.1.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def radialPatchInequalities (a c b l u : ℝ) : Fin 6 → Cover → ℝ :=
  ![fun x ↦ x 0-a,fun x ↦ c-x 0,fun x ↦ x 2,fun x ↦ b-x 2,
    fun x ↦ x 1-l*x 2,fun x ↦ u*x 2-x 1]

lemma radialPatchInequalities_contDiff (a c b l u : ℝ) (i : Fin 6) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPatchInequalities a c b l u i) := by
  have hc (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover ↦ x j) :=
    (EuclideanSpace.proj j : Cover →L[ℝ] ℝ).contDiff
  fin_cases i
  · exact (hc 0).sub contDiff_const
  · exact contDiff_const.sub (hc 0)
  · exact hc 2
  · exact contDiff_const.sub (hc 2)
  · exact (hc 1).sub (contDiff_const.mul (hc 2))
  · exact (contDiff_const.mul (hc 2)).sub (hc 1)

lemma mem_radialPatchOpen (a c b l u : ℝ) (x : Cover) :
    x ∈ strictPatchOpen (radialPatchInequalities a c b l u) ↔
      a < x 0 ∧ x 0 < c ∧ 0 < x 2 ∧ x 2 < b ∧ l*x 2 < x 1 ∧ x 1 < u*x 2 := by
  simp [strictPatchOpen,radialPatchInequalities,Fin.forall_fin_succ,sub_pos]

lemma mem_radialPatchClosed (a c b l u : ℝ) (x : Cover) :
    x ∈ strictPatchClosed (radialPatchInequalities a c b l u) ↔
      a ≤ x 0 ∧ x 0 ≤ c ∧ 0 ≤ x 2 ∧ x 2 ≤ b ∧ l*x 2 ≤ x 1 ∧ x 1 ≤ u*x 2 := by
  simp [strictPatchClosed,radialPatchInequalities,Fin.forall_fin_succ,sub_nonneg]

lemma radialPatchClosed_isCompact (a c b l u : ℝ) :
    IsCompact (strictPatchClosed (radialPatchInequalities a c b l u)) := by
  let M := (|l|+|u|)*|b|
  have hK : IsCompact (coverPrismCoordinates ⁻¹' (Icc a c ×ˢ (Icc (-M) M ×ˢ Icc 0 b))) :=
    coverPrismCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  apply hK.of_isClosed_subset
  · have he : strictPatchClosed (radialPatchInequalities a c b l u) =
        ⋂ i : Fin 6, {x | 0 ≤ radialPatchInequalities a c b l u i x} := by ext; simp [strictPatchClosed]
    rw [he]
    exact isClosed_iInter (fun i ↦ isClosed_le continuous_const
      (radialPatchInequalities_contDiff a c b l u i).continuous)
  intro x hx
  obtain ⟨ha,hc,h0,hb,hl,hu⟩ := (mem_radialPatchClosed a c b l u x).mp hx
  have hbb : x 2 ≤ |b| := hb.trans (le_abs_self b)
  have hlow : -M ≤ x 1 := by
    have hp := mul_le_mul_of_nonneg_left hbb (abs_nonneg l)
    have hq := mul_le_mul_of_nonneg_right (neg_abs_le l) h0
    have hr := mul_nonneg (abs_nonneg u) (abs_nonneg b)
    dsimp [M]; nlinarith
  have hupp : x 1 ≤ M := by
    have hp := mul_le_mul_of_nonneg_left hbb (abs_nonneg u)
    have hq := mul_le_mul_of_nonneg_right (le_abs_self u) h0
    have hr := mul_nonneg (abs_nonneg l) (abs_nonneg b)
    dsimp [M]; nlinarith
  exact ⟨⟨ha,hc⟩,⟨hlow,hupp⟩,h0,hb⟩

lemma radialPatchOpen_disjoint {a c b l u l' u' : ℝ} (hul : u ≤ l') :
    Disjoint (strictPatchOpen (radialPatchInequalities a c b l u))
      (strictPatchOpen (radialPatchInequalities a c b l' u')) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨_,_,h0,_,_,hu⟩ := (mem_radialPatchOpen a c b l u x).mp hx
  obtain ⟨_,_,_,_,hl,_⟩ := (mem_radialPatchOpen a c b l' u' x).mp hy
  have hh := mul_le_mul_of_nonneg_right hul h0.le
  linarith

lemma radialFaceIsometry_preimage_patch {a c b l u v : ℝ} (hl : l < v) (hu : v < u) :
    radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u) =
      {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < Real.sqrt (1+v^2)*b} := by
  ext y
  rw [Set.mem_preimage,mem_radialPatchOpen]
  change (a < y 0 ∧ y 0 < c ∧ 0 < (1/Real.sqrt (1+v^2))*y 1 ∧
    (1/Real.sqrt (1+v^2))*y 1 < b ∧
    l*((1/Real.sqrt (1+v^2))*y 1) < (v/Real.sqrt (1+v^2))*y 1 ∧
    (v/Real.sqrt (1+v^2))*y 1 < u*((1/Real.sqrt (1+v^2))*y 1)) ↔ _
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  have he : (v/Real.sqrt (1+v^2))*y 1 = v*((1/Real.sqrt (1+v^2))*y 1) := by ring
  rw [he]
  have hs : (1/Real.sqrt (1+v^2))*y 1 = y 1/Real.sqrt (1+v^2) := by ring
  rw [hs]
  constructor
  · rintro ⟨ha,hc,h0,hb,_,_⟩
    exact ⟨ha,hc,(div_pos_iff_of_pos_right hd).mp h0,
      by have hh := (div_lt_iff₀ hd).mp hb; simpa only [mul_comm] using hh⟩
  · rintro ⟨ha,hc,h0,hb⟩
    have hp : 0 < y 1/Real.sqrt (1+v^2) := div_pos h0 hd
    exact ⟨ha,hc,hp,(div_lt_iff₀ hd).mpr (by simpa only [mul_comm] using hb),
      mul_lt_mul_of_pos_right hl hp,mul_lt_mul_of_pos_right hu hp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeFaceCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).trans
    { toLinearEquiv :=
        { toFun := fun y ↦ (y 0,y 1)
          invFun := fun z ↦ ![z.1,z.2]
          left_inv := by intro y; ext i; fin_cases i <;> rfl
          right_inv := by intro z; rfl
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

lemma planeFaceCoordinates_measurePreserving : MeasurePreserving planeFaceCoordinates :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

lemma radial_face_patch_area {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u) :
    volume.real (radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u)) =
      (c-a)*b*Real.sqrt (1+v^2) := by
  rw [radialFaceIsometry_preimage_patch hl hu]
  have he : {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < Real.sqrt (1+v^2)*b} =
      planeFaceCoordinates ⁻¹' (Ioo a c ×ˢ Ioo 0 (Real.sqrt (1+v^2)*b)) := by
    ext y; change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _)); tauto
  rw [he,Measure.real,planeFaceCoordinates_measurePreserving.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_prod,ENNReal.toReal_mul]
  change volume.real (Ioo a c)*volume.real (Ioo 0 (Real.sqrt (1+v^2)*b)) = _
  rw [Real.volume_real_Ioo_of_le hac,Real.volume_real_Ioo_of_le (mul_nonneg (Real.sqrt_nonneg _) hb)]
  ring

lemma integral_plane_coordinate_rectangle {f : Plane → ℝ} (hf : Continuous f)
    {a c d : ℝ} (hac : a ≤ c) (hd : 0 ≤ d) :
    (∫ y in {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < d}, f y) =
      ∫ t in a..c, ∫ s in (0 : ℝ)..d, f (WithLp.toLp 2 ![t,s]) := by
  have he : {y : Plane | a < y 0 ∧ y 0 < c ∧ 0 < y 1 ∧ y 1 < d} =
      planeFaceCoordinates ⁻¹' (Ioo a c ×ˢ Ioo 0 d) := by
    ext y; change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _)); tauto
  rw [he]
  have hm := planeFaceCoordinates_measurePreserving.restrict_preimage
    (s := Ioo a c ×ˢ Ioo 0 d) (measurableSet_Ioo.prod measurableSet_Ioo)
  have hms := hm.symm planeFaceCoordinates.toHomeomorph.toMeasurableEquiv
  rw [← hms.integral_comp planeFaceCoordinates.symm.toHomeomorph.measurableEmbedding]
  let f' : ℝ × ℝ → ℝ := fun z ↦ f (planeFaceCoordinates.symm z)
  have hc : Continuous f' := hf.comp planeFaceCoordinates.symm.continuous
  have hi : IntegrableOn f' (Ioo a c ×ˢ Ioo 0 d) (volume.prod volume) :=
    (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  change (∫ z in Ioo a c ×ˢ Ioo 0 d, f' z) = _
  rw [Measure.volume_eq_prod,setIntegral_prod f' hi,
    setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hac]
  apply intervalIntegral.integral_congr
  intro t _
  change (∫ s in Ioo 0 d, f' (t,s)) = _
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le hd]
  rfl

theorem radial_face_patch_integral {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {f : Cover → ℝ} (hf : Continuous f) :
    (∫ y in radialFaceIsometry v ⁻¹' strictPatchOpen (radialPatchInequalities a c b l u),
      f (radialFaceIsometry v y)) =
      Real.sqrt (1+v^2) *
        ∫ t in a..c, ∫ s in (0 : ℝ)..b, f (WithLp.toLp 2 ![t,v*s,s]) := by
  rw [radialFaceIsometry_preimage_patch hl hu,
    integral_plane_coordinate_rectangle (f := fun y ↦ f (radialFaceIsometry v y))
      (hf.comp (radialFaceIsometry v).continuous) hac
      (mul_nonneg (Real.sqrt_nonneg _) hb),← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have hd : Real.sqrt (1+v^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne'
  have he (s : ℝ) : radialFaceIsometry v (WithLp.toLp 2 ![t,s]) =
      WithLp.toLp 2 ![t,v*(s/Real.sqrt (1+v^2)),s/Real.sqrt (1+v^2)] := by
    ext i; fin_cases i <;> simp [radialFaceIsometry] <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_comp_div (fun s ↦ f (WithLp.toLp 2 ![t,v*s,s])) hd]
  simp only [zero_div,mul_div_cancel_left₀ _ hd,smul_eq_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0)
    {U : Set Cover} (hU : MeasurableSet U) (f : Cover → ℝ) :
    (∫ y in normalPlaneEmbedding n ⁻¹' U, f (normalPlaneEmbedding n y)) =
      ∫ y in T ⁻¹' U, f (T y) := by
  have he := integral_normalPlane_eq_isometry hn T hT (U.indicator f)
  have he' (S : Plane → Cover) : (fun y ↦ U.indicator f (S y)) =
      (S ⁻¹' U).indicator (fun y ↦ f (S y)) := by
    funext y; by_cases hy : S y ∈ U <;> simp [hy]
  have hmn : MeasurableSet (normalPlaneEmbedding n ⁻¹' U) :=
    hU.preimage (normalPlaneLinearIsometry n).continuous.measurable
  rw [he',he',integral_indicator hmn,
    integral_indicator (hU.preimage T.continuous.measurable)] at he
  exact he

lemma real_volume_normalPlane_eq_isometry {n : Cover} (hn : ‖n‖ = 1)
    (T : Plane →ₗᵢ[ℝ] Cover) (hT : ∀ y, ⟪n,T y⟫ = 0)
    {U : Set Cover} (hU : MeasurableSet U) :
    volume.real (normalPlaneEmbedding n ⁻¹' U) = volume.real (T ⁻¹' U) := by
  have hh := setIntegral_normalPlane_eq_isometry hn T hT hU (fun _ ↦ (1 : ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

lemma inner_radialFaceNormal (v : ℝ) (x : Cover) :
    ⟪radialFaceNormal v,x⟫ = (x 1-v*x 2)/Real.sqrt (1+v^2) := by
  simp [radialFaceNormal,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three]
  ring

theorem radial_face_flux {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {F : Cover → Cover} (hF : Continuous F) :
    (∫ y in normalPlaneEmbedding (radialFaceNormal v) ⁻¹'
        strictPatchOpen (radialPatchInequalities a c b l u),
      ⟪radialFaceNormal v,F (normalPlaneEmbedding (radialFaceNormal v) y)⟫) =
      ∫ t in a..c, ∫ s in (0 : ℝ)..b,
        F (WithLp.toLp 2 ![t,v*s,s]) 1-v*F (WithLp.toLp 2 ![t,v*s,s]) 2 := by
  rw [setIntegral_normalPlane_eq_isometry (radialFaceNormal_norm v) (radialFaceIsometry v)
    (radialFaceIsometry_perp v) (measurableSet_strictPatchOpen
      (fun i ↦ (radialPatchInequalities_contDiff a c b l u i).continuous))
    (fun x ↦ ⟪radialFaceNormal v,F x⟫)]
  rw [radial_face_patch_integral (f := fun x ↦ ⟪radialFaceNormal v,F x⟫) hac hb hl hu (continuous_const.inner hF)]
  simp_rw [inner_radialFaceNormal]
  simp_rw [div_eq_mul_inv,intervalIntegral.integral_mul_const]
  rw [mul_left_comm,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne',mul_one]

theorem neg_radial_face_flux {a c b l u v : ℝ}
    (hac : a ≤ c) (hb : 0 ≤ b) (hl : l < v) (hu : v < u)
    {F : Cover → Cover} (hF : Continuous F) :
    (∫ y in normalPlaneEmbedding (-radialFaceNormal v) ⁻¹'
        strictPatchOpen (radialPatchInequalities a c b l u),
      ⟪-radialFaceNormal v,F (normalPlaneEmbedding (-radialFaceNormal v) y)⟫) =
      -(∫ t in a..c, ∫ s in (0 : ℝ)..b,
        F (WithLp.toLp 2 ![t,v*s,s]) 1-v*F (WithLp.toLp 2 ![t,v*s,s]) 2) := by
  have hn : ‖-radialFaceNormal v‖ = 1 := by rw [norm_neg,radialFaceNormal_norm]
  have hperp (y : Plane) : ⟪-radialFaceNormal v,radialFaceIsometry v y⟫ = 0 := by
    rw [inner_neg_left,radialFaceIsometry_perp,neg_zero]
  rw [setIntegral_normalPlane_eq_isometry hn (radialFaceIsometry v) hperp
    (measurableSet_strictPatchOpen (fun i ↦ (radialPatchInequalities_contDiff a c b l u i).continuous))
    (fun x ↦ ⟪-radialFaceNormal v,F x⟫)]
  simp_rw [inner_neg_left]
  rw [integral_neg]
  congr 1
  rw [radial_face_patch_integral (f := fun x ↦ ⟪radialFaceNormal v,F x⟫) hac hb hl hu (continuous_const.inner hF)]
  simp_rw [inner_radialFaceNormal]
  simp_rw [div_eq_mul_inv,intervalIntegral.integral_mul_const]
  rw [mul_left_comm,mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity : 0 < 1+v^2)).ne',mul_one]

end CubicTorus

end
end

end

end OAI
