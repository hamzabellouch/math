import OAI.Geometry.CylinderCovering.Nilpotent.ShearDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.C1

namespace OAI

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Topology ContDiff
namespace RuledApproximation.NilpotentShear

lemma field_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) :
    ContDiff ℝ 1 (field ell v c f) := by
  exact contDiff_const.add ((hf.comp ell.contDiff).smul contDiff_const)

lemma field_hasFDerivAt {f : ℝ → ℝ} {p : Plane}
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) (hf : DifferentiableAt ℝ f (ell p)) :
    HasFDerivAt (field ell v c f)
      (((deriv f (ell p)) • ell).smulRight v) p := by
  exact ((hf.hasDerivAt.comp_hasFDerivAt p ell.hasFDerivAt).smul_const v).const_add c

lemma field_fderiv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c p : Plane) :
    fderiv ℝ (field ell v c f) p =
      (((deriv f (ell p)) • ell).smulRight v) :=
  (field_hasFDerivAt ell v c (hf.differentiable one_ne_zero (ell p))).fderiv

lemma field_squareZero {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c p : Plane) (hv : ell v = 0) :
    (fderiv ℝ (field ell v c f) p).comp (fderiv ℝ (field ell v c f) p) = 0 := by
  rw [field_fderiv hf]
  ext q i
  simp [ContinuousLinearMap.comp_apply, hv]

lemma field_smoothNear {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) (D : Set Plane) :
    SmoothNear 1 D (field ell v c f) :=
  ⟨univ, isOpen_univ, subset_univ D, (field_contDiff hf ell v c).contDiffOn⟩

lemma signedSquare_hasDerivAt (y : ℝ) :
    HasDerivAt signedSquare (2 * |y|) y := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · convert! (hasDerivAt_id y).mul (hasDerivAt_abs_neg hy) using 1
    simp only [abs_of_neg hy, id_eq]
    ring
  · have hsmall : (fun x : ℝ => |x|) =o[𝓝 0] (fun _ => (1 : ℝ)) := by
      apply (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr
      simpa using (continuous_abs.continuousAt (x := (0 : ℝ))).tendsto
    have hprod := (isBigO_refl (fun x : ℝ => x) (𝓝 (0 : ℝ))).mul_isLittleO hsmall
    apply HasDerivAt.of_isLittleO
    simpa [signedSquare] using hprod
  · convert! (hasDerivAt_id y).mul (hasDerivAt_abs_pos hy) using 1
    simp only [abs_of_pos hy, id_eq]
    ring

lemma signedSquare_deriv : deriv signedSquare = fun y => 2 * |y| :=
  funext fun y => (signedSquare_hasDerivAt y).deriv

lemma signedSquare_contDiff : ContDiff ℝ 1 signedSquare := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y => (signedSquare_hasDerivAt y).differentiableAt, ?_⟩
  rw [signedSquare_deriv]
  exact continuous_const.mul continuous_abs

lemma signedSquare_not_contDiff_two : ¬ ContDiff ℝ 2 signedSquare := by
  intro h
  have hd : ContDiff ℝ 1 (deriv signedSquare) := h.deriv'
  have ha := (hd.differentiable one_ne_zero 0).const_mul (1/2 : ℝ)
  have he : (fun y : ℝ => (1/2 : ℝ) * deriv signedSquare y) = abs := by
    funext y
    rw [signedSquare_deriv]
    ring
  rw [he] at ha
  exact not_differentiableAt_abs_zero ha

lemma signedSquare_not_contDiffAt_two_zero : ¬ ContDiffAt ℝ 2 signedSquare 0 := by
  intro h
  have hd : ContDiffAt ℝ 1 (deriv signedSquare) 0 := h.derivWithin (by norm_num)
  have ha := (hd.differentiableAt one_ne_zero).const_mul (1/2 : ℝ)
  have he : (fun y : ℝ => (1/2 : ℝ) * deriv signedSquare y) = abs := by
    funext y
    rw [signedSquare_deriv]
    ring
  rw [he] at ha
  exact not_differentiableAt_abs_zero ha

lemma signedSquareField_contDiff : ContDiff ℝ 1 signedSquareField :=
  field_contDiff signedSquare_contDiff _ _ _

lemma signedSquareField_squareZero (p : Plane) :
    (fderiv ℝ signedSquareField p).comp (fderiv ℝ signedSquareField p) = 0 :=
  field_squareZero signedSquare_contDiff _ _ _ p (by rfl)

lemma signedSquareField_apply (p : Plane) :
    signedSquareField p = vec2 (signedSquare (p 1)) 0 := by
  ext i
  fin_cases i <;> simp [signedSquareField, field, vec2]

lemma signedSquareField_not_contDiff_two : ¬ ContDiff ℝ 2 signedSquareField := by
  intro h
  apply signedSquare_not_contDiff_two
  have hc : ContDiff ℝ 2 (fun y : ℝ => y • vec2 0 1) :=
    contDiff_id.smul contDiff_const
  have hh := (EuclideanSpace.proj 0).contDiff.comp (h.comp hc)
  convert! hh using 1
  funext y
  simp [signedSquareField_apply, vec2]

lemma signedSquareField_not_contDiffAt_two_zero :
    ¬ ContDiffAt ℝ 2 signedSquareField 0 := by
  intro h
  apply signedSquare_not_contDiffAt_two_zero
  have hc : ContDiffAt ℝ 2 (fun y : ℝ => y • vec2 0 1) 0 :=
    (contDiff_id.smul contDiff_const).contDiffAt
  have h' : ContDiffAt ℝ 2 signedSquareField ((0 : ℝ) • vec2 0 1) := by simpa using h
  have hh := (EuclideanSpace.proj 0).contDiff.contDiffAt.comp 0 (h'.comp 0 hc)
  convert! hh using 1
  funext y
  simp [signedSquareField_apply, vec2]

lemma signedSquareField_not_smoothNear_two {D : Set Plane} (hD : 0 ∈ D) :
    ¬ SmoothNear 2 D signedSquareField := by
  rintro ⟨U, hU, hDU, hdiff⟩
  exact signedSquareField_not_contDiffAt_two_zero
    (hdiff.contDiffAt (hU.mem_nhds (hDU hD)))

lemma signedSquareField_fderiv_zero : fderiv ℝ signedSquareField 0 = 0 := by
  rw [signedSquareField, field_fderiv signedSquare_contDiff, signedSquare_deriv]
  simp

lemma signedSquareField_large_derivative :
    1 < ‖fderiv ℝ signedSquareField (vec2 0 1)‖ := by
  have he : (fderiv ℝ signedSquareField (vec2 0 1)) (vec2 0 1) = vec2 2 0 := by
    rw [signedSquareField, field_fderiv signedSquare_contDiff, signedSquare_deriv]
    ext i
    fin_cases i <;> norm_num [vec2]
  have hn1 : ‖vec2 0 1‖ = 1 := by
    have hs := norm_plane_sq (vec2 0 1)
    norm_num at hs
    rcases hs with hs | hs
    · exact hs
    · linarith [norm_nonneg (vec2 0 1)]
  have hn2 : ‖vec2 2 0‖ = 2 := by
    have hs := norm_plane_sq (vec2 2 0)
    norm_num at hs
    nlinarith [norm_nonneg (vec2 2 0)]
  have hb := (fderiv ℝ signedSquareField (vec2 0 1)).le_opNorm (vec2 0 1)
  rw [he, hn1, hn2, mul_one] at hb
  linarith

theorem field_physical_cover {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) (hv : ell v = 0)
    {D : Set Plane} (hD : IsCompact D) {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D (field ell v c f) 1)
      (h * (∫ p in D, physicalWeight h (field ell v c f p)) + eps) :=
  nilpotent_physical_cover hh hD (field_smoothNear hf ell v c D)
    (fun p _ => field_squareZero hf ell v c p hv) heps

theorem signedSquareField_physical_cover {D : Set Plane} (hD : IsCompact D)
    {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D signedSquareField 1)
      (h * (∫ p in D, physicalWeight h (signedSquareField p)) + eps) :=
  field_physical_cover signedSquare_contDiff _ _ _ (by rfl) hD hh heps

theorem field_weighted_cover {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) (hv : ell v = 0)
    {D : Set Plane} (hD : IsCompact D) {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) :
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D (field ell v c f) 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (field ell v c f b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i)) :=
  nilpotentC1 D (field ell v c f) hD (field_smoothNear hf ell v c D)
    (fun p _ => field_squareZero hf ell v c p hv) h eps hh heps

theorem field_null_domain_cover {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (ell : Plane →L[ℝ] ℝ) (v c : Plane) (hv : ell v = 0)
    {D : Set Plane} (hD : IsCompact D) (hzero : volume D = 0)
    {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h D (field ell v c f) 1) eps := by
  have hc := field_physical_cover hf ell v c hv hD hh heps
  simpa [setIntegral_measure_zero (fun p => physicalWeight h (field ell v c f p)) hzero]
    using hc

end RuledApproximation.NilpotentShear

end

end OAI
