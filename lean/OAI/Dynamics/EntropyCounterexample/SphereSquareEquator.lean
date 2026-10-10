import OAI.Dynamics.EntropyCounterexample.SphereDoubling

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

abbrev Equator := {x : Sphere // x.val 2 = 0}

def circleInclusion (z : Circle) : Sphere :=
  ⟨!₂[(z : ℂ).re, (z : ℂ).im, 0], by
    have hz : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
    have hn : ‖(!₂[(z : ℂ).re, (z : ℂ).im, 0] : Ambient)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [Fin.sum_univ_succ] using hz
    have hnorm : ‖(!₂[(z : ℂ).re, (z : ℂ).im, 0] : Ambient)‖ = 1 := by
      nlinarith [norm_nonneg (!₂[(z : ℂ).re, (z : ℂ).im, 0] : Ambient)]
    simpa using hnorm⟩

@[simp] theorem circleInclusion_zero (z : Circle) : (circleInclusion z).val 0 = (z : ℂ).re := rfl
@[simp] theorem circleInclusion_one (z : Circle) : (circleInclusion z).val 1 = (z : ℂ).im := rfl
@[simp] theorem circleInclusion_two (z : Circle) : (circleInclusion z).val 2 = 0 := rfl

lemma continuous_circleInclusion : Continuous circleInclusion := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val
  · exact continuous_const

theorem sphereMap_circleInclusion (z : Circle) :
    sphereMap (circleInclusion z) = circleInclusion (z ^ 2) := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [sphereMap, ambientMap, circleInclusion, pow_two, Complex.mul_re, Complex.mul_im]
  ; ring

def equatorCoordinate (x : Equator) : Circle :=
  ⟨⟨x.val.val 0, x.val.val 1⟩, by
    have hx := sphere_equation x.val
    rw [x.property] at hx
    have hn : Complex.normSq (⟨x.val.val 0, x.val.val 1⟩ : ℂ) = 1 := by
      simpa [Complex.normSq_apply, pow_two] using hx
    apply mem_sphere_zero_iff_norm.mpr
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, ← Complex.normSq_eq_norm_sq]
    simpa using hn⟩

lemma circleInclusion_equatorCoordinate (x : Equator) :
    circleInclusion (equatorCoordinate x) = x.val := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [circleInclusion, equatorCoordinate, x.property]

lemma equatorCoordinate_circleInclusion (z : Circle) :
    equatorCoordinate ⟨circleInclusion z, circleInclusion_two z⟩ = z := by
  apply Circle.ext
  rfl

lemma continuous_equatorCoordinate : Continuous equatorCoordinate := by
  apply Continuous.subtype_mk
  have h0 : Continuous (fun x : Equator => x.val.val 0) :=
    (EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  have h1 : Continuous (fun x : Equator => x.val.val 1) :=
    (EuclideanSpace.proj 1).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  convert (Complex.continuous_ofReal.comp h0).add
    ((Complex.continuous_ofReal.comp h1).mul
      (continuous_const : Continuous (fun _ : Equator => Complex.I))) using 1
  funext x
  apply Complex.ext <;> simp

def circleEquatorHomeomorph : Circle ≃ₜ Equator where
  toFun z := ⟨circleInclusion z, circleInclusion_two z⟩
  invFun := equatorCoordinate
  left_inv := equatorCoordinate_circleInclusion
  right_inv x := Subtype.ext (circleInclusion_equatorCoordinate x)
  continuous_toFun := continuous_circleInclusion.subtype_mk _
  continuous_invFun := continuous_equatorCoordinate

@[simp] theorem sphereMap_third_eq_zero_iff (x : Sphere) :
    (sphereMap x).val 2 = 0 ↔ x.val 2 = 0 := by
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) = 0 ↔ _
  rw [div_eq_zero_iff]
  simp [ne_of_gt (denominator_pos x.val)]

@[simp] theorem sphereMap_third_pos_iff (x : Sphere) :
    0 < (sphereMap x).val 2 ↔ 0 < x.val 2 := by
  change 0 < (2 * x.val 2) / (1 + x.val 2 ^ 2) ↔ _
  rw [div_pos_iff_of_pos_right (denominator_pos x.val)]
  exact mul_pos_iff_of_pos_left (by norm_num)

@[simp] theorem sphereMap_third_neg_iff (x : Sphere) :
    (sphereMap x).val 2 < 0 ↔ x.val 2 < 0 := by
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) < 0 ↔ _
  rw [div_lt_iff₀ (denominator_pos x.val)]
  constructor <;> intro h <;> nlinarith

def equatorSquare (x : Equator) : Equator :=
  ⟨sphereMap x.val, (sphereMap_third_eq_zero_iff x.val).mpr x.property⟩

lemma continuous_equatorSquare : Continuous equatorSquare :=
  (continuous_sphereMap.comp continuous_subtype_val).subtype_mk _

theorem equatorSquare_circleEquatorHomeomorph (z : Circle) :
    equatorSquare (circleEquatorHomeomorph z) = circleEquatorHomeomorph (z ^ 2) :=
  Subtype.ext (sphereMap_circleInclusion z)

lemma eq_south_iff (x : Sphere) : x = south ↔ x.val 2 = -1 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have he := sphere_equation x
    have h0 : x.val 0 = 0 := by nlinarith [sq_nonneg (x.val 1), sq_nonneg (x.val 0)]
    have h1 : x.val 1 = 0 := by nlinarith [sq_nonneg (x.val 1), sq_nonneg (x.val 0)]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [south, h0, h1, h, Matrix.cons_val_two]

@[simp] theorem sphereMap_eq_south_iff (x : Sphere) :
    sphereMap x = south ↔ x = south := by
  rw [eq_south_iff, eq_south_iff]
  change (2 * x.val 2) / (1 + x.val 2 ^ 2) = -1 ↔ _
  rw [div_eq_iff (ne_of_gt (denominator_pos x.val))]
  constructor <;> intro h <;> nlinarith

theorem sphereMap_mapsTo_puncturedNorth :
    Set.MapsTo sphereMap {x | x ≠ north} {x | x ≠ north} := by
  intro x hx
  exact mt (sphereMap_eq_north_iff x).mp hx

theorem sphereMap_mapsTo_puncturedSouth :
    Set.MapsTo sphereMap {x | x ≠ south} {x | x ≠ south} := by
  intro x hx
  exact mt (sphereMap_eq_south_iff x).mp hx

end Problem340.SphereDoubling

end

end OAI
