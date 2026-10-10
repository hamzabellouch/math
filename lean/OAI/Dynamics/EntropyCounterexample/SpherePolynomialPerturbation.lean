import OAI.Dynamics.EntropyCounterexample.SphereDoubling

namespace OAI

noncomputable section
namespace Problem340.SpherePolynomialPerturbation

abbrev Ambient := SphereDoubling.Ambient
abbrev Sphere := SphereDoubling.Sphere

def numeratorRe (c : ℂ) (x : Ambient) : ℝ :=
  x 0 ^ 2 - x 1 ^ 2 + c.re * (1 - x 2) ^ 2

def numeratorIm (c : ℂ) (x : Ambient) : ℝ :=
  2 * x 0 * x 1 + c.im * (1 - x 2) ^ 2

def squaredNumeratorReduced (c : ℂ) (x : Ambient) : ℝ :=
  (1 + x 2) ^ 2 +
    2 * (c.re * (x 0 ^ 2 - x 1 ^ 2) + c.im * (2 * x 0 * x 1)) +
    (c.re ^ 2 + c.im ^ 2) * (1 - x 2) ^ 2

def denominator (c : ℂ) (x : Ambient) : ℝ :=
  squaredNumeratorReduced c x + (1 - x 2) ^ 2

def ambientMap (c : ℂ) (x : Ambient) : Ambient :=
  !₂[2 * numeratorRe c x / denominator c x,
     2 * numeratorIm c x / denominator c x,
     (squaredNumeratorReduced c x - (1 - x 2) ^ 2) / denominator c x]

lemma numerator_identity (c : ℂ) (x : Sphere) :
    numeratorRe c x.val ^ 2 + numeratorIm c x.val ^ 2 =
      (1 - x.val 2) ^ 2 * squaredNumeratorReduced c x.val := by
  have hx := SphereDoubling.sphere_equation x
  have he : x.val 0 ^ 2 + x.val 1 ^ 2 = 1 - x.val 2 ^ 2 := by linarith
  dsimp [numeratorRe, numeratorIm, squaredNumeratorReduced]
  calc
    _ = (x.val 0 ^ 2 + x.val 1 ^ 2) ^ 2 +
        2 * (1 - x.val 2) ^ 2 *
          (c.re * (x.val 0 ^ 2 - x.val 1 ^ 2) + c.im * (2 * x.val 0 * x.val 1)) +
        (c.re ^ 2 + c.im ^ 2) * (1 - x.val 2) ^ 4 := by ring
    _ = _ := by rw [he]; ring

lemma denominator_pos (c : ℂ) (x : Sphere) : 0 < denominator c x.val := by
  by_cases hz : x.val 2 = 1
  · have hx := SphereDoubling.sphere_equation x
    have hx0 : x.val 0 = 0 := by nlinarith [sq_nonneg (x.val 1)]
    have hx1 : x.val 1 = 0 := by nlinarith [sq_nonneg (x.val 0)]
    norm_num [denominator, squaredNumeratorReduced, hz, hx0, hx1]
  · have hd : 0 < (1 - x.val 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hz))
    have hi := numerator_identity c x
    have hA : 0 ≤ squaredNumeratorReduced c x.val := by
      nlinarith [sq_nonneg (numeratorRe c x.val), sq_nonneg (numeratorIm c x.val)]
    dsimp [denominator]
    linarith

lemma ambientMap_mem_sphere (c : ℂ) (x : Sphere) :
    ambientMap c x.val ∈ Metric.sphere (0 : Ambient) 1 := by
  have hi := numerator_identity c x
  have hd := ne_of_gt (denominator_pos c x)
  have hn : ‖ambientMap c x.val‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ, ambientMap, Matrix.cons_val_zero,
      Fin.sum_univ_zero, add_zero]
    change (2 * numeratorRe c x.val / denominator c x.val) ^ 2 +
      ((2 * numeratorIm c x.val / denominator c x.val) ^ 2 +
        ((squaredNumeratorReduced c x.val - (1 - x.val 2) ^ 2) /
          denominator c x.val) ^ 2) = 1
    field_simp
    dsimp [denominator]
    nlinarith [hi]
  have hnorm : ‖ambientMap c x.val‖ = 1 := by
    nlinarith [norm_nonneg (ambientMap c x.val)]
  simpa using hnorm

def sphereMap (c : ℂ) (x : Sphere) : Sphere :=
  ⟨ambientMap c x.val, ambientMap_mem_sphere c x⟩

def complexCoordinate (x : Ambient) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

def stereoCoordinate (x : Ambient) : ℂ :=
  complexCoordinate x / ((1 - x 2 : ℝ) : ℂ)

lemma numerator_complex (c : ℂ) (x : Ambient) :
    (numeratorRe c x : ℂ) + (numeratorIm c x : ℂ) * Complex.I =
      complexCoordinate x ^ 2 + c * ((1 - x 2 : ℝ) : ℂ) ^ 2 := by
  apply Complex.ext <;>
    simp [numeratorRe, numeratorIm, complexCoordinate, pow_two,
      Complex.mul_re, Complex.mul_im]; ring

lemma complexCoordinate_ambientMap (c : ℂ) (x : Ambient) :
    complexCoordinate (ambientMap c x) =
      2 * ((numeratorRe c x : ℂ) + (numeratorIm c x : ℂ) * Complex.I) /
        (denominator c x : ℂ) := by
  change ((2 * numeratorRe c x / denominator c x : ℝ) : ℂ) +
    ((2 * numeratorIm c x / denominator c x : ℝ) : ℂ) * Complex.I = _
  push_cast
  ring

lemma one_sub_height (c : ℂ) (x : Ambient) (hd : denominator c x ≠ 0) :
    1 - ambientMap c x 2 = 2 * (1 - x 2) ^ 2 / denominator c x := by
  change 1 - (squaredNumeratorReduced c x - (1 - x 2) ^ 2) / denominator c x = _
  field_simp
  simp only [denominator]
  ring

theorem stereoCoordinate_ambientMap (c : ℂ) (x : Sphere) (hx : x.val 2 ≠ 1) :
    stereoCoordinate (ambientMap c x.val) = stereoCoordinate x.val ^ 2 + c := by
  have hd : denominator c x.val ≠ 0 := ne_of_gt (denominator_pos c x)
  have hz : (1 - x.val 2 : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hdC : (denominator c x.val : ℂ) ≠ 0 := by exact_mod_cast hd
  have hzC : ((1 - x.val 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
  unfold stereoCoordinate
  rw [complexCoordinate_ambientMap, one_sub_height c x.val hd, numerator_complex]
  push_cast at hzC ⊢
  field_simp [hdC, hzC]

lemma ambientMap_zero (x : Ambient) : ambientMap 0 x = SphereDoubling.ambientMap x := by
  have h1 : (1 + x 2 ^ 2) ≠ 0 := ne_of_gt (SphereDoubling.denominator_pos x)
  have h2 : (1 + x 2) ^ 2 + (1 - x 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x 2)]
  ext i
  fin_cases i <;>
    simp [ambientMap, SphereDoubling.ambientMap, numeratorRe, numeratorIm,
      squaredNumeratorReduced, denominator] <;>
    field_simp <;> ring

@[simp] lemma sphereMap_zero (x : Sphere) : sphereMap 0 x = SphereDoubling.sphereMap x := by
  apply Subtype.ext
  exact ambientMap_zero x.val

lemma sphereMap_fixes_north (c : ℂ) (x : Sphere) (hx : x.val 2 = 1) :
    sphereMap c x = x := by
  have he := SphereDoubling.sphere_equation x
  have hx0 : x.val 0 = 0 := by nlinarith [sq_nonneg (x.val 1)]
  have hx1 : x.val 1 = 0 := by nlinarith [sq_nonneg (x.val 0)]
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [sphereMap, ambientMap, numeratorRe, numeratorIm, squaredNumeratorReduced,
      denominator, hx, hx0, hx1]

lemma sphereMap_avoids_north (c : ℂ) (x : Sphere) (hx : x.val 2 ≠ 1) :
    (sphereMap c x).val 2 ≠ 1 := by
  have hd := denominator_pos c x
  have hz : 0 < (1 - x.val 2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hx))
  have hp : 0 < 1 - ambientMap c x.val 2 := by
    rw [one_sub_height c x.val (ne_of_gt hd)]
    positivity
  change ambientMap c x.val 2 ≠ 1
  linarith

def domain : Set (ℂ × Ambient) := {p | denominator p.1 p.2 ≠ 0}

lemma contDiff_numeratorRe (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × Ambient => numeratorRe p.1 p.2) := by
  have hr : ContDiff ℝ n (fun p : ℂ × Ambient => p.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  unfold numeratorRe
  fun_prop

lemma contDiff_numeratorIm (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × Ambient => numeratorIm p.1 p.2) := by
  have hi : ContDiff ℝ n (fun p : ℂ × Ambient => p.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  unfold numeratorIm
  fun_prop

lemma contDiff_squaredNumeratorReduced (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × Ambient => squaredNumeratorReduced p.1 p.2) := by
  have hr : ContDiff ℝ n (fun p : ℂ × Ambient => p.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have hi : ContDiff ℝ n (fun p : ℂ × Ambient => p.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  unfold squaredNumeratorReduced
  fun_prop

lemma contDiff_denominator (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : ℂ × Ambient => denominator p.1 p.2) := by
  unfold denominator
  exact (contDiff_squaredNumeratorReduced n).add (by fun_prop)

lemma isOpen_domain : IsOpen domain := by
  exact isOpen_ne.preimage (contDiff_denominator 1).continuous

lemma sphere_mem_domain (c : ℂ) (x : Sphere) : (c, x.val) ∈ domain :=
  ne_of_gt (denominator_pos c x)

lemma contDiffOn_ambientMap (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun p : ℂ × Ambient => ambientMap p.1 p.2) domain := by
  apply contDiffOn_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ n (fun p : ℂ × Ambient =>
      2 * numeratorRe p.1 p.2 / denominator p.1 p.2) domain
    exact (contDiff_const.mul (contDiff_numeratorRe n)).contDiffOn.div
      (contDiff_denominator n).contDiffOn (fun _ hp => hp)
  · change ContDiffOn ℝ n (fun p : ℂ × Ambient =>
      2 * numeratorIm p.1 p.2 / denominator p.1 p.2) domain
    exact (contDiff_const.mul (contDiff_numeratorIm n)).contDiffOn.div
      (contDiff_denominator n).contDiffOn (fun _ hp => hp)
  · change ContDiffOn ℝ n (fun p : ℂ × Ambient =>
      (squaredNumeratorReduced p.1 p.2 - (1 - p.2 2) ^ 2) /
        denominator p.1 p.2) domain
    exact ((contDiff_squaredNumeratorReduced n).sub (by fun_prop)).contDiffOn.div
      (contDiff_denominator n).contDiffOn (fun _ hp => hp)

lemma contDiffAt_ambientMap (n : WithTop ℕ∞) (c : ℂ) (x : Sphere) :
    ContDiffAt ℝ n (fun p : ℂ × Ambient => ambientMap p.1 p.2) (c, x.val) :=
  (contDiffOn_ambientMap n).contDiffAt (isOpen_domain.mem_nhds (sphere_mem_domain c x))

lemma continuous_jointSphereMap : Continuous (fun p : ℂ × Sphere => sphereMap p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (contDiffOn_ambientMap 1).continuousOn.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun p => sphere_mem_domain p.1 p.2)

theorem exists_smooth_ambient_neighborhood (c : ℂ) (x : Sphere) :
    ∃ U : Set (ℂ × Ambient), IsOpen U ∧ (c, x.val) ∈ U ∧
      ContDiffOn ℝ 1 (fun p : ℂ × Ambient => ambientMap p.1 p.2) U :=
  ⟨domain, isOpen_domain, sphere_mem_domain c x, contDiffOn_ambientMap 1⟩

section Homotopy

variable {X : Type*} [TopologicalSpace X]

def jointMap : C(ℂ × Sphere, Sphere) :=
  ⟨fun p => sphereMap p.1 p.2, continuous_jointSphereMap⟩

def inducedMap (C : C(X, ℂ)) (z : C(X, Sphere)) : C(X, Sphere) :=
  jointMap.comp (C.prodMk z)

def fadeParameters (C : C(X, ℂ)) (z : C(X, Sphere)) :
    C(unitInterval × X, ℂ × Sphere) where
  toFun p := (p.1.val • C p.2, z p.2)
  continuous_toFun := by
    have ht : Continuous (fun p : unitInterval × X => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact (ht.smul (C.continuous.comp continuous_snd)).prodMk
      (z.continuous.comp continuous_snd)

def fadeHomotopy (C : C(X, ℂ)) (z : C(X, Sphere)) :
    ContinuousMap.Homotopy (inducedMap 0 z) (inducedMap C z) where
  toContinuousMap := jointMap.comp (fadeParameters C z)
  map_zero_left x := by
    change sphereMap ((0 : ℝ) • C x) (z x) = sphereMap 0 (z x)
    simp only [zero_smul]
  map_one_left x := by
    change sphereMap ((1 : ℝ) • C x) (z x) = sphereMap (C x) (z x)
    simp only [one_smul]

@[simp] lemma inducedMap_zero_apply (z : C(X, Sphere)) (x : X) :
    inducedMap 0 z x = SphereDoubling.sphereMap (z x) := by
  exact sphereMap_zero (z x)

end Homotopy

end Problem340.SpherePolynomialPerturbation

end

end OAI
