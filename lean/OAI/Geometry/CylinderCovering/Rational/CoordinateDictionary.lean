import OAI.Geometry.CylinderCovering.Rational.DictionaryDefinitions
import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions
import OAI.Geometry.CylinderCovering.Rational.Similarity

namespace OAI

noncomputable section
namespace RationalDictionary

theorem c0_pos : 0 < c0 := by unfold c0; positivity
theorem ell_pos : 0 < ell := by unfold ell; positivity
theorem ell_ne_zero : ell ≠ 0 := ne_of_gt ell_pos

theorem c0_sq : c0 ^ 2 = 1 / 2 := by
  unfold c0
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem ell_eq_half_c0 : ell = c0 / 2 := by unfold ell c0; ring

theorem two_ell_eq_c0 : 2 * ell = c0 := by rw [ell_eq_half_c0]; ring

theorem ell_mul_c0 : ell * c0 = 1 / 4 := by
  rw [ell_eq_half_c0]
  nlinarith [c0_sq]

theorem ell_sq : ell ^ 2 = 1 / 8 := by
  rw [ell_eq_half_c0]
  nlinarith [c0_sq]

theorem hasDerivAt_g {d0 s : ℝ} (hs : s + d0 ≠ 0) :
    HasDerivAt (g d0) (gPrime d0 s) s := by
  change HasDerivAt (fun t : ℝ => (1 + d0) / (t + d0)) (-(1 + d0) / (s + d0) ^ 2) s
  have hc : HasDerivAt (fun _ : ℝ => 1 + d0) (0 : ℝ) s := hasDerivAt_const s (1 + d0)
  have hd : HasDerivAt (fun t : ℝ => t + d0) (1 : ℝ) s := (hasDerivAt_id s).add_const d0
  convert hc.fun_div hd hs using 1
  first | rfl | simp

theorem a0_eq_sq_mul_v1 {d0 : ℝ} (hd : 1 + d0 ≠ 0) (u : ℝ) :
    a0 d0 u = u ^ 2 * v1 d0 u 1 := by
  unfold a0 A0 B0 v1 g gPrime
  rw [c0_sq]
  field_simp
  ring

theorem centeredPadding_eq_margin_mul_tilt_sq {d0 : ℝ} (hd : 1 + d0 ≠ 0)
    (eta0 k : ℝ) :
    centeredPadding eta0 k = centeredMargin d0 eta0 * centeredTilt d0 k ^ 2 := by
  unfold centeredPadding centeredMargin centeredTilt
  field_simp
  ring

theorem parameter_positivity {d0 eta0 k : ℝ} (hd : 0 < d0) (he : 0 < eta0)
    (hk : 0 < k) :
    0 < centeredRegularization d0 ∧ 0 < centeredTilt d0 k ∧
    0 < centeredPadding eta0 k ∧ 0 < centeredMargin d0 eta0 := by
  unfold centeredRegularization centeredTilt centeredPadding centeredMargin
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem cutoff_iff (s : ℝ) : s ≤ 3 / 2 ↔ -(1 / 4 : ℝ) ≤ (1 - s) / 2 := by
  constructor <;> intro hs <;> linarith

theorem wedge_iff (u s : ℝ) :
    |u| ≤ c0 * s ↔ 2 * |ell * u| ≤ 1 / 2 - (1 - s) / 2 := by
  rw [abs_mul, abs_of_pos ell_pos]
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left h ell_pos.le
    have he : ell * (c0 * s) = s / 4 := by rw [← mul_assoc, ell_mul_c0]; ring
    rw [he] at hm
    linarith
  · intro h
    have hm := mul_le_mul_of_nonneg_left h c0_pos.le
    have he : c0 * (2 * (ell * |u|)) = |u| / 2 := by
      calc
        c0 * (2 * (ell * |u|)) = 2 * (ell * c0) * |u| := by ring
        _ = |u| / 2 := by rw [ell_mul_c0]; ring
    rw [he] at hm
    nlinarith

theorem v1_dictionary {d0 s : ℝ} (hs : s + d0 ≠ 0) (u : ℝ) :
    v1 d0 u s = -4 * (1 + d0) *
      SlopeRational.a (d0 / 2) (ell * u) ((1 - s) / 2) := by
  have hr : SlopeRational.radius ((1 - s) / 2) = s / 2 := by
    unfold SlopeRational.radius; ring
  unfold v1 g gPrime SlopeRational.a
  rw [hr, mul_pow, ell_sq, c0_sq]
  have hden : s / 2 + d0 / 2 = (s + d0) / 2 := by ring
  rw [hden]
  field_simp
  ring

theorem v2_dictionary {d0 s : ℝ} (hs : s + d0 ≠ 0) (u : ℝ) :
    v2 d0 u s = 2 * Real.sqrt 2 * (1 + d0) *
      SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2) := by
  have hr : SlopeRational.radius ((1 - s) / 2) = s / 2 := by
    unfold SlopeRational.radius; ring
  unfold v2 g SlopeRational.b ell
  rw [hr]
  have hroot : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp

theorem ceiling_dictionary {d0 : ℝ} (hd : 1 + d0 ≠ 0) (u : ℝ) :
    SlopeRational.ceilingPolynomial (d0 / 2) (ell * u) =
      a0 d0 u / (32 * (1 + d0) ^ 2) := by
  unfold SlopeRational.ceilingPolynomial SlopeRational.alpha
    SlopeRational.ceilingCoefficient SlopeRational.ceilingConstant
    SlopeRational.ceilingQuadratic a0 A0 B0
  rw [mul_pow, ell_sq, c0_sq]
  have hh : (1 / 2 : ℝ) + d0 / 2 = (1 + d0) / 2 := by ring
  have ht : 1 + 2 * (d0 / 2) = 1 + d0 := by ring
  rw [hh, ht]
  field_simp
  ring

theorem ceiling_inequality_iff {d0 : ℝ} (hd : 1 + d0 ≠ 0) (eta0 k u s : ℝ) :
    s ≤ 1 + k ^ 2 * (a0 d0 u + eta0) ↔
      -(centeredTilt d0 k) ^ 2 *
        SlopeRational.ceilingPolynomial (d0 / 2) (ell * u) - centeredPadding eta0 k ≤
        (1 - s) / 2 := by
  rw [ceiling_dictionary hd]
  have he : (centeredTilt d0 k) ^ 2 *
      (a0 d0 u / (32 * (1 + d0) ^ 2)) = k ^ 2 * a0 d0 u / 2 := by
    unfold centeredTilt
    field_simp
    ring
  rw [neg_mul, he]
  unfold centeredPadding
  constructor <;> intro h <;> nlinarith

theorem labelDomain_iff {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) (p : Plane) :
    p ∈ uncenteredDomain d0 eta0 k ↔
      labelMap p ∈ SlopeRational.labelDomain (centeredRegularization d0)
        (centeredTilt d0 k) (centeredPadding eta0 k) := by
  have hd' : 1 + d0 ≠ 0 := by linarith
  change (0 ≤ p 1 ∧ p 1 ≤ 3 / 2 ∧ |p 0| ≤ c0 * p 1 ∧
      p 1 ≤ 1 + k ^ 2 * (a0 d0 (p 0) + eta0)) ↔
    (2 * |ell * p 0| ≤ 1 / 2 - (1 - p 1) / 2 ∧
      -(1 / 4 : ℝ) ≤ (1 - p 1) / 2 ∧
      -(centeredTilt d0 k) ^ 2 *
        SlopeRational.ceilingPolynomial (d0 / 2) (ell * p 0) - centeredPadding eta0 k ≤
          (1 - p 1) / 2)
  rw [← wedge_iff, ← cutoff_iff, ← ceiling_inequality_iff hd']
  constructor
  · rintro ⟨_, hcut, hw, hcap⟩
    exact ⟨hw, hcut, hcap⟩
  · rintro ⟨hw, hcut, hcap⟩
    have hnonneg : 0 ≤ c0 * p 1 := (abs_nonneg (p 0)).trans hw
    have hs : 0 ≤ p 1 := (mul_nonneg_iff_of_pos_left c0_pos).mp hnonneg
    exact ⟨hs, hcut, hw, hcap⟩

@[simp] theorem vec2_zero (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] theorem vec2_one (x y : ℝ) : vec2 x y 1 = y := rfl
@[simp] theorem vec3_zero (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] theorem vec3_one (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] theorem vec3_two (x y z : ℝ) : vec3 x y z 2 = z := rfl

@[simp] theorem labelMap_inverseLabelMap (p : Plane) :
    labelMap (inverseLabelMap p) = p := by
  ext i
  fin_cases i <;> simp [labelMap, inverseLabelMap, vec2]
  field_simp [ell_ne_zero]

@[simp] theorem inverseLabelMap_labelMap (p : Plane) :
    inverseLabelMap (labelMap p) = p := by
  ext i
  fin_cases i <;> simp [labelMap, inverseLabelMap, vec2] <;> field_simp [ell_ne_zero]
  ring

@[simp] theorem reflectLabel_involutive (p : Plane) : reflectLabel (reflectLabel p) = p := by
  ext i
  fin_cases i <;> simp [reflectLabel, vec2]

@[simp] theorem reflectLabel_domain_iff (d eps q : ℝ) (p : Plane) :
    reflectLabel p ∈ SlopeRational.labelDomain d eps q ↔
      p ∈ SlopeRational.labelDomain d eps q := by
  simp [reflectLabel, vec2, SlopeRational.labelDomain, SlopeRational.wedge,
    SlopeRational.ceilingPolynomial, SlopeRational.ceilingCoefficient]

theorem free_coordinate_iff (r : ℝ) : |ell * r| ≤ 1 / 2 ↔ |r| ≤ 2 * c0 := by
  rw [abs_mul, abs_of_pos ell_pos]
  have he : ell * (2 * c0) = 1 / 2 := by nlinarith [ell_mul_c0]
  rw [← he]
  exact mul_le_mul_iff_right₀ ell_pos

theorem first_point_dictionary {d0 s : ℝ} (hs : s + d0 ≠ 0) (k r u : ℝ) :
    RationalSimilarity.phi (vec3 r (u + r * k * v1 d0 u s) (s + r * k * v2 d0 u s)) =
      centeredFirstPoint (d0 / 2) (centeredTilt d0 k) (-ell * r)
        (vec2 (ell * u) ((1 - s) / 2)) := by
  have h1 := v1_dictionary hs u
  have h2 := v2_dictionary hs u
  have hroot : 2 * Real.sqrt 2 * ell = 1 := by
    unfold ell
    field_simp
  ext i
  fin_cases i
  · rfl
  · change ell * (u + r * k * v1 d0 u s) =
      ell * u + centeredTilt d0 k * (-ell * r) *
        SlopeRational.a (d0 / 2) (ell * u) ((1 - s) / 2)
    rw [h1]
    unfold centeredTilt
    ring
  · change ell * (1 - (s + r * k * v2 d0 u s)) =
      c0 * ((1 - s) / 2 + centeredTilt d0 k * (-ell * r) *
        SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2))
    rw [h2, ← two_ell_eq_c0]
    unfold centeredTilt
    calc
      ell * (1 - (s + r * k * (2 * Real.sqrt 2 * (1 + d0) *
          SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2)))) =
        ell * (1 - s) - (2 * Real.sqrt 2 * ell) * r * k * (1 + d0) *
          SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2) := by ring
      _ = ell * (1 - s) - (8 * ell ^ 2) * r * k * (1 + d0) *
          SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2) := by
        rw [hroot, ell_sq]; norm_num
      _ = _ := by ring

@[simp] theorem centered_a_neg (d Y T : ℝ) :
    SlopeRational.a d (-Y) T = SlopeRational.a d Y T := by
  simp [SlopeRational.a]

@[simp] theorem centered_b_neg (d Y T : ℝ) :
    SlopeRational.b d (-Y) T = -SlopeRational.b d Y T := by
  unfold SlopeRational.b
  ring

theorem second_point_dictionary {d0 s : ℝ} (hs : s + d0 ≠ 0) (k r u : ℝ) :
    RationalSimilarity.phi
      (vec3 (u + (-r) * k * v1 d0 u s) r (2 - (s + (-r) * k * v2 d0 u s))) =
      centeredSecondPoint (d0 / 2) (centeredTilt d0 k) (ell * r)
        (vec2 (-(ell * u)) ((1 - s) / 2)) := by
  have h := first_point_dictionary hs k (-r) u
  ext i
  fin_cases i
  · have hh := congrArg (fun p : Space => p 1) h
    change ell * (u + (-r) * k * v1 d0 u s) =
      ell * u + centeredTilt d0 k * (-ell * (-r)) *
        SlopeRational.a (d0 / 2) (ell * u) ((1 - s) / 2) at hh
    change -ell * (u + (-r) * k * v1 d0 u s) =
      -(ell * u) - centeredTilt d0 k * (ell * r) *
        SlopeRational.a (d0 / 2) (-(ell * u)) ((1 - s) / 2)
    rw [centered_a_neg]
    nlinarith only [hh]
  · rfl
  · have hh := congrArg (fun p : Space => p 2) h
    change ell * (1 - (s + (-r) * k * v2 d0 u s)) =
      c0 * ((1 - s) / 2 + centeredTilt d0 k * (-ell * (-r)) *
        SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2)) at hh
    change ell * (1 - (2 - (s + (-r) * k * v2 d0 u s))) =
      -c0 * ((1 - s) / 2 - centeredTilt d0 k * (ell * r) *
        SlopeRational.b (d0 / 2) (-(ell * u)) ((1 - s) / 2))
    rw [centered_b_neg]
    nlinarith only [hh]

theorem first_lineMap_dictionary {d0 : ℝ} (hd : 0 < d0) {eta0 k : ℝ}
    {p : Plane} (hp : p ∈ uncenteredDomain d0 eta0 k) (r : ℝ) :
    RationalSimilarity.phi (vec3 r (lineMap d0 k r p 0) (lineMap d0 k r p 1)) =
      centeredFirstPoint (centeredRegularization d0) (centeredTilt d0 k) (-ell * r)
        (labelMap p) := by
  have hs : p 1 + d0 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)
  exact first_point_dictionary hs k r (p 0)

theorem second_lineMap_dictionary {d0 : ℝ} (hd : 0 < d0) {eta0 k : ℝ}
    {p : Plane} (hp : p ∈ uncenteredDomain d0 eta0 k) (r : ℝ) :
    RationalSimilarity.phi (vec3 (lineMap d0 k (-r) p 0) r (2 - lineMap d0 k (-r) p 1)) =
      centeredSecondPoint (centeredRegularization d0) (centeredTilt d0 k) (ell * r)
        (reflectLabel (labelMap p)) := by
  have hs : p 1 + d0 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)
  exact second_point_dictionary hs k r (p 0)

theorem phi_image_firstSweep {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RationalSimilarity.phi '' uncenteredFirstSweep d0 eta0 k =
      centeredFirstSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    refine ⟨labelMap p, (labelDomain_iff hd eta0 k p).mp hp, -ell * r, ?_, ?_⟩
    · simpa only [neg_mul, abs_neg] using (free_coordinate_iff r).mpr hr
    · exact first_lineMap_dictionary hd hp r
  · rintro z ⟨p, hp, x, hx, rfl⟩
    let p0 := inverseLabelMap p
    have hp0 : p0 ∈ uncenteredDomain d0 eta0 k := by
      apply (labelDomain_iff hd eta0 k p0).mpr
      simpa [p0] using hp
    let r := -x / ell
    have hxr : -ell * r = x := by dsimp [r]; field_simp [ell_ne_zero]
    have hr : |r| ≤ 2 * c0 := by
      apply (free_coordinate_iff r).mp
      have hr' : ell * r = -x := by linarith [hxr]
      simpa only [hr', abs_neg] using hx
    refine ⟨vec3 r (lineMap d0 k r p0 0) (lineMap d0 k r p0 1),
      ⟨p0, hp0, r, hr, rfl⟩, ?_⟩
    rw [first_lineMap_dictionary hd hp0, hxr]
    simp [p0]

theorem phi_image_secondSweep {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RationalSimilarity.phi '' uncenteredSecondSweep d0 eta0 k =
      centeredSecondSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    refine ⟨reflectLabel (labelMap p), ?_, ell * r,
      (free_coordinate_iff r).mpr hr, second_lineMap_dictionary hd hp r⟩
    exact (reflectLabel_domain_iff _ _ _ _).mpr ((labelDomain_iff hd eta0 k p).mp hp)
  · rintro z ⟨p, hp, y, hy, rfl⟩
    let p0 := inverseLabelMap (reflectLabel p)
    have hp0 : p0 ∈ uncenteredDomain d0 eta0 k := by
      apply (labelDomain_iff hd eta0 k p0).mpr
      simp only [p0, labelMap_inverseLabelMap]
      exact (reflectLabel_domain_iff _ _ _ _).mpr hp
    let r := y / ell
    have hyr : ell * r = y := by dsimp [r]; field_simp [ell_ne_zero]
    have hr : |r| ≤ 2 * c0 := by
      apply (free_coordinate_iff r).mp
      simpa only [hyr] using hy
    refine ⟨vec3 (lineMap d0 k (-r) p0 0) r (2 - lineMap d0 k (-r) p0 1),
      ⟨p0, hp0, r, hr, rfl⟩, ?_⟩
    rw [second_lineMap_dictionary hd hp0, hyr]
    simp [p0]

theorem sweep_dictionary {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RationalSimilarity.phi '' uncenteredFirstSweep d0 eta0 k =
      centeredFirstSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    RationalSimilarity.phi '' uncenteredSecondSweep d0 eta0 k =
      centeredSecondSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) :=
  ⟨phi_image_firstSweep hd eta0 k, phi_image_secondSweep hd eta0 k⟩

theorem v1_divider {d0 : ℝ} (hd : 1 + d0 ≠ 0) (u : ℝ) :
    v1 d0 u 1 = A0 d0 + B0 d0 * u ^ 2 := by
  unfold v1 g gPrime A0 B0
  field_simp
  ring

theorem threshold_sum {d0 : ℝ} (hd : 1 + d0 ≠ 0) (k x y : ℝ) :
    threshold d0 k x y + threshold d0 k (-y) x =
      2 + k ^ 2 * B0 d0 * (x ^ 2 - y ^ 2) ^ 2 := by
  unfold threshold a0
  rw [v1_divider hd y, v1_divider hd x]
  ring

theorem threshold_dichotomy {d0 : ℝ} (hd : 0 < d0) (k x y z : ℝ) :
    z ≤ threshold d0 k x y ∨ 2 - z ≤ threshold d0 k (-y) x := by
  have hd' : 1 + d0 ≠ 0 := by linarith
  have hb : 0 < B0 d0 := by unfold B0; positivity
  have hp : 0 ≤ k ^ 2 * B0 d0 * (x ^ 2 - y ^ 2) ^ 2 := by positivity
  have hsum := threshold_sum hd' k x y
  by_cases hz : z ≤ threshold d0 k x y
  · exact Or.inl hz
  · right
    linarith

theorem squared_slope_dictionary {d0 s : ℝ} (hs : s + d0 ≠ 0) (k u : ℝ) :
    centeredTilt d0 k ^ 2 *
      (SlopeRational.a (d0 / 2) (ell * u) ((1 - s) / 2) ^ 2 +
        c0 ^ 2 * SlopeRational.b (d0 / 2) (ell * u) ((1 - s) / 2) ^ 2) =
      k ^ 2 * (v1 d0 u s ^ 2 + v2 d0 u s ^ 2) := by
  rw [v1_dictionary hs u, v2_dictionary hs u, c0_sq]
  unfold centeredTilt
  have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsqrt]
  ring

theorem coordinate_identity {d0 : ℝ} (hd : 0 < d0) (eta0 k : ℝ) :
    RationalSimilarity.phi '' RationalSimilarity.uncenteredTetrahedron =
      RationalSimilarity.centeredTetrahedron ∧
    RationalSimilarity.phi '' uncenteredFirstSweep d0 eta0 k =
      centeredFirstSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    RationalSimilarity.phi '' uncenteredSecondSweep d0 eta0 k =
      centeredSecondSweep (centeredRegularization d0) (centeredTilt d0 k)
        (centeredPadding eta0 k) ∧
    centeredPadding eta0 k = centeredMargin d0 eta0 * centeredTilt d0 k ^ 2 ∧
    ∀ S : Set Space,
      (MeasureTheory.Measure.euclideanHausdorffMeasure 2 (RationalSimilarity.phi '' S)).toReal =
        (1 / 8 : ℝ) * (MeasureTheory.Measure.euclideanHausdorffMeasure 2 S).toReal := by
  exact ⟨RationalSimilarity.phi_image_tetrahedron, phi_image_firstSweep hd eta0 k,
    phi_image_secondSweep hd eta0 k,
    centeredPadding_eq_margin_mul_tilt_sq (by linarith) eta0 k,
    RationalSimilarity.phi_area⟩

end RationalDictionary

end

end OAI
