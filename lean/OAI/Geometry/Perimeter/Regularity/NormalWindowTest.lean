import OAI.Geometry.Perimeter.Regularity.FiberMomentIntegration

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

abbrev normalProjection (v : Euc n) : Euc n →L[ℝ] normalPlane v :=
  (normalPlane v).orthogonalProjectionOnto

@[simp] theorem normalProjection_fiber (v : Euc n) (y : normalPlane v) (s : ℝ) :
    normalProjection v ((y:Euc n)+s•v) = y := by
  have hv : normalProjection v v = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      ((ℝ ∙ v).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self v))
  rw [map_add,map_smul,hv,smul_zero,add_zero]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y

@[simp] theorem normal_fiber_inner {v : Euc n} (hv : ‖v‖ = 1)
    (y : normalPlane v) (s : ℝ) : inner ℝ v ((y:Euc n)+s•v) = s := by
  rw [inner_add_right,real_inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property,
    real_inner_self_eq_norm_sq,hv]
  ring

def normalWindowTest (v : Euc n) (φ : normalPlane v → ℝ) (b : ℝ) (m : ℕ)
    (x : Euc n) : ℝ :=
  {z : Euc n | |inner ℝ v z| ≤ b}.indicator
    (fun z ↦ φ (normalProjection v z)*(inner ℝ v z)^m) x

theorem normalWindowTest_measurable {v : Euc n} {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (b : ℝ) (m : ℕ) : Measurable (normalWindowTest v φ b m) :=
  ((hφ.comp (normalProjection v).continuous).measurable.mul
    ((continuous_const.inner continuous_id).pow m).measurable).indicator
      (isClosed_le (continuous_const.inner continuous_id).abs continuous_const).measurableSet

theorem normalWindowTest_bound {v : Euc n} {φ : normalPlane v → ℝ}
    {M b : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M) (hb : 0 ≤ b) (m : ℕ) (x : Euc n) :
    ‖normalWindowTest v φ b m x‖ ≤ M*b^m := by
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  by_cases hx : |inner ℝ v x| ≤ b
  · simp only [normalWindowTest,Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_left hx,norm_mul,norm_pow,
      Real.norm_eq_abs]
    exact mul_le_mul (hM _) (pow_le_pow_left₀ (abs_nonneg _) hx m) (pow_nonneg (abs_nonneg _) _) hM0
  · simp only [normalWindowTest,Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_right hx,norm_zero]
    exact mul_nonneg hM0 (pow_nonneg hb _)

theorem normalWindowTest_continuousAt {v : Euc n} {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) {b : ℝ} (m : ℕ) {x : Euc n} (hx : |inner ℝ v x| < b) :
    ContinuousAt (normalWindowTest v φ b m) x := by
  have he : ∀ᶠ z in 𝓝 x, |inner ℝ v z| < b :=
    (continuous_const.inner continuous_id).abs.continuousAt.eventually (gt_mem_nhds hx)
  have hc : Continuous (fun z ↦ φ (normalProjection v z)*(inner ℝ v z)^m) :=
    (hφ.comp (normalProjection v).continuous).mul ((continuous_const.inner continuous_id).pow m)
  apply hc.continuousAt.congr
  filter_upwards [he] with z hz
  simp only [normalWindowTest,Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_left hz.le]

@[simp] theorem normalCoordinates_mem_normalCylinder {v : Euc n} (hv : ‖v‖ = 1)
    (K : Set (normalPlane v)) (b : ℝ) (y : normalPlane v) (s : ℝ) :
    (y:Euc n)+s•v ∈ normalCylinder v hv K b ↔ y ∈ K ∧ s ∈ Icc (-b) b := by
  change normalCoordinates v hv (y,s) ∈ normalCoordinates v hv '' (K ×ˢ Icc (-b) b) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have he' : z = (y,s) := (normalCoordinates v hv).injective he
    simpa only [he',Set.mem_prod] using hz
  · intro h
    exact ⟨(y,s),h,rfl⟩

theorem normalWindowTest_eq_indicator {v : Euc n} (hv : ‖v‖ = 1)
    (φ : normalPlane v → ℝ) (b : ℝ) (m : ℕ) :
    normalWindowTest v φ b m = (normalCylinder v hv (tsupport φ) b).indicator
      (fun x ↦ φ (normalProjection v x)*(inner ℝ v x)^m) := by
  funext x
  obtain ⟨⟨y,s⟩,rfl⟩ := (normalCoordinates v hv).surjective x
  simp only [normalCoordinates_apply]
  by_cases hy : y ∈ tsupport φ
  · by_cases hs : s ∈ Icc (-b) b
    · have hs' : |s| ≤ b := abs_le.mpr hs
      simp [normalWindowTest,normal_fiber_inner hv,hs',normalCoordinates_mem_normalCylinder,hy,hs]
    · have hs' : ¬ |s| ≤ b := fun h ↦ hs (abs_le.mp h)
      simp [normalWindowTest,normal_fiber_inner hv,hs',normalCoordinates_mem_normalCylinder,hy,hs]
  · have hz : φ y=0 := image_eq_zero_of_notMem_tsupport hy
    simp [normalWindowTest,normal_fiber_inner hv,normalCoordinates_mem_normalCylinder,
      hy,hz,Set.indicator_apply]

theorem normalWindowTest_integrable {v : Euc n} (hv : ‖v‖ = 1)
    {φ : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (b : ℝ) (m : ℕ) : Integrable (normalWindowTest v φ b m) volume := by
  rw [normalWindowTest_eq_indicator hv]
  have hf : Continuous (fun x ↦ φ (normalProjection v x)*(inner ℝ v x)^m) :=
    (hφ.comp (normalProjection v).continuous).mul ((continuous_const.inner continuous_id).pow m)
  exact (hf.continuousOn.integrableOn_compact (isCompact_normalCylinder hv hcφ b)).integrable_indicator
    (isCompact_normalCylinder hv hcφ b).measurableSet

theorem normalWindowTest_support_subset {v : Euc n} (hv : ‖v‖ = 1)
    (φ : normalPlane v → ℝ) (b : ℝ) (m : ℕ) :
    Function.support (normalWindowTest v φ b m) ⊆ normalCylinder v hv (tsupport φ) b := by
  rw [normalWindowTest_eq_indicator hv]
  exact Set.support_indicator_subset

theorem normalWindowTest_mul_integrable {v : Euc n} (hv : ‖v‖ = 1)
    {φ : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (b : ℝ) (m : ℕ) {g : Euc n → ℝ} (hg : Continuous g) :
    Integrable (fun x ↦ normalWindowTest v φ b m x*g x) volume := by
  rw [normalWindowTest_eq_indicator hv]
  have he : (fun x ↦ (normalCylinder v hv (tsupport φ) b).indicator
      (fun z ↦ φ (normalProjection v z)*(inner ℝ v z)^m) x*g x) =
      (normalCylinder v hv (tsupport φ) b).indicator
        (fun x ↦ φ (normalProjection v x)*(inner ℝ v x)^m*g x) := by
    funext x
    by_cases hx : x ∈ normalCylinder v hv (tsupport φ) b <;> simp [hx]
  rw [he]
  have hf : Continuous (fun x ↦ φ (normalProjection v x)*(inner ℝ v x)^m*g x) :=
    ((hφ.comp (normalProjection v).continuous).mul ((continuous_const.inner continuous_id).pow m)).mul hg
  exact (hf.continuousOn.integrableOn_compact (isCompact_normalCylinder hv hcφ b)).integrable_indicator
    (isCompact_normalCylinder hv hcφ b).measurableSet

theorem normalWindowTest_support_norm {v : Euc n} (hv : ‖v‖ = 1)
    (φ : normalPlane v → ℝ) (b δ R : ℝ) (m : ℕ)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R) {x : Euc n}
    (hx : normalWindowTest v φ b m x ≠ 0) : ‖x‖+δ ≤ R := by
  obtain ⟨⟨y,s⟩,⟨hy,hs⟩,rfl⟩ := normalWindowTest_support_subset hv φ b m hx
  have h := norm_add_le (y:Euc n) (s•v)
  rw [norm_smul,hv,mul_one,Real.norm_eq_abs] at h
  have hs' : |s| ≤ b := abs_le.mpr hs
  have hyR := hKR y hy
  change ‖(y:Euc n)‖+b+δ ≤ R at hyR
  change ‖(y:Euc n)+s•v‖+δ ≤ R
  linarith

theorem normalWindowTest_integral {v : Euc n} (hv : ‖v‖ = 1)
    {φ : normalPlane v → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {b : ℝ} (hb : 0 ≤ b) (m : ℕ) {g : Euc n → ℝ} (hg : Continuous g) :
    (∫ x, normalWindowTest v φ b m x*g x) =
      ∫ y in tsupport φ, φ y*(∫ s in (-b)..b, s^m*g ((y:Euc n)+s•v)) := by
  let f : Euc n → ℝ := fun x ↦ φ (normalProjection v x)*(inner ℝ v x)^m*g x
  have hf : Continuous f := ((hφ.comp (normalProjection v).continuous).mul
    ((continuous_const.inner continuous_id).pow m)).mul hg
  have he : (fun x ↦ normalWindowTest v φ b m x*g x) =
      (normalCylinder v hv (tsupport φ) b).indicator f := by
    funext x
    obtain ⟨⟨y,s⟩,rfl⟩ := (normalCoordinates v hv).surjective x
    simp only [normalCoordinates_apply]
    by_cases hy : y ∈ tsupport φ
    · by_cases hs : s ∈ Icc (-b) b
      · have hs' : |s| ≤ b := abs_le.mpr hs
        simp [normalWindowTest,normal_fiber_inner hv,hs',normalCoordinates_mem_normalCylinder,
          hy,hs,f]
      · have hs' : ¬ |s| ≤ b := fun h ↦ hs (abs_le.mp h)
        simp [normalWindowTest,normal_fiber_inner hv,hs',normalCoordinates_mem_normalCylinder,
          hy,hs,f]
    · have hz : φ y=0 := image_eq_zero_of_notMem_tsupport hy
      simp [normalWindowTest,normal_fiber_inner hv,normalCoordinates_mem_normalCylinder,
        hy,f,hz,Set.indicator_apply]
  rw [he,integral_indicator (isCompact_normalCylinder hv hcφ b).measurableSet,
    integral_normalCylinder hv hcφ hb hf]
  apply setIntegral_congr_fun hcφ.measurableSet
  intro y _
  dsimp only [f]
  simp_rw [normalProjection_fiber,normal_fiber_inner hv]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

end RPISingularHarnack

end

end OAI
