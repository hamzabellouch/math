import Mathlib

namespace OAI

noncomputable section

namespace Problem340.SphereDoubling

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Ambient) (1 : ℝ)

def ambientMap (x : Ambient) : Ambient :=
  !₂[(x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2),
     (2 * x 0 * x 1) / (1 + x 2 ^ 2),
     (2 * x 2) / (1 + x 2 ^ 2)]

lemma denominator_pos (x : Ambient) : 0 < 1 + x 2 ^ 2 := by positivity

lemma contDiff_ambientMap (n : WithTop ℕ∞) : ContDiff ℝ n ambientMap := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun x : Ambient => (x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))
  · change ContDiff ℝ n (fun x : Ambient => (2 * x 0 * x 1) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))
  · change ContDiff ℝ n (fun x : Ambient => (2 * x 2) / (1 + x 2 ^ 2))
    fun_prop (disch := intro x; exact ne_of_gt (denominator_pos x))

lemma sphere_equation (x : Sphere) :
    (x.val 0) ^ 2 + (x.val 1) ^ 2 + (x.val 2) ^ 2 = 1 := by
  have hx : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hn := EuclideanSpace.real_norm_sq_eq x.val
  simpa [hx, Fin.sum_univ_succ, add_assoc] using hn.symm

lemma ambientMap_mem_sphere (x : Sphere) : ambientMap x.val ∈ Metric.sphere (0 : Ambient) 1 := by
  have hx := sphere_equation x
  have hd := ne_of_gt (denominator_pos x.val)
  have hn : ‖ambientMap x.val‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ, ambientMap]
    field_simp
    have hsq := congrArg (fun t : ℝ => t ^ 2) hx
    nlinarith
  have hnorm : ‖ambientMap x.val‖ = 1 := by nlinarith [norm_nonneg (ambientMap x.val)]
  simpa using hnorm

def sphereMap (x : Sphere) : Sphere := ⟨ambientMap x.val, ambientMap_mem_sphere x⟩

lemma continuous_sphereMap : Continuous sphereMap := by
  exact ((contDiff_ambientMap 1).continuous.comp continuous_subtype_val).subtype_mk _

def stereoCoordinate (x : Ambient) : ℂ :=
  ((x 0 : ℂ) + Complex.I * (x 1 : ℂ)) / (1 - (x 2 : ℂ))

lemma ambientMap_third_ne_one {x : Ambient} (hx : x 2 ≠ 1) :
    ambientMap x 2 ≠ 1 := by
  intro h
  change (2 * x 2) / (1 + x 2 ^ 2) = 1 at h
  have h' := (div_eq_one_iff_eq (ne_of_gt (denominator_pos x))).mp h
  apply hx
  nlinarith [sq_nonneg (x 2 - 1)]

lemma stereoCoordinate_ambientMap {x : Ambient} (hx : x 2 ≠ 1) :
    stereoCoordinate (ambientMap x) = stereoCoordinate x ^ 2 := by
  have hd : (1 : ℂ) + (x 2 : ℂ) ^ 2 ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (denominator_pos x)))
  have hz : (1 : ℂ) - (x 2 : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hx)))
  change (((((x 0 ^ 2 - x 1 ^ 2) / (1 + x 2 ^ 2) : ℝ) : ℂ) +
    Complex.I * (((2 * x 0 * x 1) / (1 + x 2 ^ 2) : ℝ) : ℂ)) /
    (1 - (((2 * x 2) / (1 + x 2 ^ 2) : ℝ) : ℂ))) = _
  unfold stereoCoordinate
  push_cast
  have hden : (1 : ℂ) - 2 * (x 2 : ℂ) / (1 + (x 2 : ℂ) ^ 2) =
      (1 - (x 2 : ℂ)) ^ 2 / (1 + (x 2 : ℂ) ^ 2) := by
    field_simp
    ring
  rw [hden]
  field_simp [hd, hz]
  ring_nf
  simp [Complex.I_sq, sub_eq_add_neg]

def north : Sphere := ⟨!₂[0, 0, 1], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

def south : Sphere := ⟨!₂[0, 0, -1], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

def east : Sphere := ⟨!₂[1, 0, 0], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

def west : Sphere := ⟨!₂[-1, 0, 0], by
  norm_num [Metric.mem_sphere, EuclideanSpace.norm_eq, Fin.sum_univ_succ]⟩

@[simp] lemma sphereMap_north : sphereMap north = north := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, north, Matrix.cons_val_two]

@[simp] lemma sphereMap_south : sphereMap south = south := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, south, Matrix.cons_val_two]

@[simp] lemma sphereMap_east : sphereMap east = east := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, east, Matrix.cons_val_two]

@[simp] lemma sphereMap_west : sphereMap west = east := by
  apply Subtype.ext
  ext i
  fin_cases i <;> norm_num [sphereMap, ambientMap, west, east, Matrix.cons_val_two]

lemma east_ne_west : east ≠ west := by
  intro h
  have h0 := congrArg (fun x : Sphere => x.val 0) h
  norm_num [east, west] at h0

lemma not_injective_sphereMap : ¬ Function.Injective sphereMap := by
  intro h
  exact east_ne_west (h (by simp))

lemma eq_north_iff (x : Sphere) : x = north ↔ x.val 2 = 1 := by
  constructor
  · intro h
    simp [h, north, Matrix.cons_val_two]
  · intro h
    have he := sphere_equation x
    have h0 : x.val 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x.val 1)]
    have h1 : x.val 1 ^ 2 = 0 := by nlinarith [sq_nonneg (x.val 0)]
    have h0' := sq_eq_zero_iff.mp h0
    have h1' := sq_eq_zero_iff.mp h1
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [north, h0', h1', h, Matrix.cons_val_two]

@[simp] lemma sphereMap_eq_north_iff (x : Sphere) : sphereMap x = north ↔ x = north := by
  constructor
  · intro h
    apply (eq_north_iff x).mpr
    by_contra hx
    apply ambientMap_third_ne_one hx
    exact (eq_north_iff (sphereMap x)).mp h
  · intro h
    simp [h]

lemma stereoCoordinate_sphereMap {x : Sphere} (hx : x ≠ north) :
    stereoCoordinate (sphereMap x).val = stereoCoordinate x.val ^ 2 := by
  exact stereoCoordinate_ambientMap (mt (eq_north_iff x).mpr hx)

@[simp] lemma iterate_sphereMap_eq_north_iff (n : ℕ) (x : Sphere) :
    (sphereMap^[n]) x = north ↔ x = north := by
  induction n with
  | zero => simp
  | succ n ih => simpa [Function.iterate_succ_apply'] using ih

lemma stereoCoordinate_iterate_sphereMap (n : ℕ) {x : Sphere} (hx : x ≠ north) :
    stereoCoordinate ((sphereMap^[n]) x).val = stereoCoordinate x.val ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [stereoCoordinate_sphereMap (mt (iterate_sphereMap_eq_north_iff n x).mp hx), ih]
    rw [← pow_mul, pow_succ]

end Problem340.SphereDoubling

end

end OAI
