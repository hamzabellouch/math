import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SphereCaps
open scoped ContDiff Manifold
open Set
noncomputable section
abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := Metric.sphere (0 : R3) 1
abbrev Plane := ℝ × ℝ
local instance sphereCapsFinrank : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

def vec3 (a b c : ℝ) : R3 := WithLp.toLp 2 ![a,b,c]
def radiusSq (z : Plane) : ℝ := z.1 ^ 2 + z.2 ^ 2
def north (l : ℝ) (p : S2) : Plane :=
  (Real.sqrt (2 * l / (1 + (p : R3) 2)) * (p : R3) 0,
   Real.sqrt (2 * l / (1 + (p : R3) 2)) * (p : R3) 1)
def south (l : ℝ) (p : S2) : Plane :=
  (Real.sqrt (2 * l / (1 - (p : R3) 2)) * (p : R3) 0,
   -(Real.sqrt (2 * l / (1 - (p : R3) 2)) * (p : R3) 1))
def northInvAmbient (l : ℝ) (z : Plane) : R3 :=
  vec3 (z.1 * Real.sqrt (4 * l - radiusSq z) / (2 * l))
    (z.2 * Real.sqrt (4 * l - radiusSq z) / (2 * l))
    (1 - radiusSq z / (2 * l))
def southInvAmbient (l : ℝ) (z : Plane) : R3 :=
  vec3 (z.1 * Real.sqrt (4 * l - radiusSq z) / (2 * l))
    (-z.2 * Real.sqrt (4 * l - radiusSq z) / (2 * l))
    (-1 + radiusSq z / (2 * l))

def standardArea (p v w : R3) : ℝ :=
  p 0 * (v 1 * w 2 - v 2 * w 1) +
  p 1 * (v 2 * w 0 - v 0 * w 2) +
  p 2 * (v 0 * w 1 - v 1 * w 0)

@[simp] lemma vec3_apply_zero (a b c : ℝ) : vec3 a b c 0 = a := rfl
@[simp] lemma vec3_apply_one (a b c : ℝ) : vec3 a b c 1 = b := rfl
@[simp] lemma vec3_apply_two (a b c : ℝ) : vec3 a b c 2 = c := rfl
lemma sphere_equation (p : S2) :
    (p : R3) 0 ^ 2 + (p : R3) 1 ^ 2 + (p : R3) 2 ^ 2 = 1 := by
  have hp := norm_eq_of_mem_sphere p
  have hh := EuclideanSpace.real_norm_sq_eq (p : R3)
  simp only [Fin.sum_univ_three] at hh
  rw [hp] at hh
  nlinarith

lemma height_bounds (p : S2) : -1 ≤ (p : R3) 2 ∧ (p : R3) 2 ≤ 1 := by
  have h := sphere_equation p
  constructor <;> nlinarith [sq_nonneg ((p : R3) 0), sq_nonneg ((p : R3) 1)]

lemma radiusSq_nonneg (z : Plane) : 0 ≤ radiusSq z := by
  unfold radiusSq
  positivity

lemma north_radius (l : ℝ) (hl : 0 < l) (p : S2) (hp : -1 < (p : R3) 2) :
    radiusSq (north l p) = 2 * l * (1 - (p : R3) 2) := by
  have hd : 0 < 1 + (p : R3) 2 := by linarith
  have hs : Real.sqrt (2 * l / (1 + (p : R3) 2)) ^ 2 =
      2 * l / (1 + (p : R3) 2) := Real.sq_sqrt (by positivity)
  have he := sphere_equation p
  dsimp [north, radiusSq]
  simp only [mul_pow, hs]
  field_simp
  nlinarith [he]

lemma south_radius (l : ℝ) (hl : 0 < l) (p : S2) (hp : (p : R3) 2 < 1) :
    radiusSq (south l p) = 2 * l * (1 + (p : R3) 2) := by
  have hd : 0 < 1 - (p : R3) 2 := by linarith
  have hs : Real.sqrt (2 * l / (1 - (p : R3) 2)) ^ 2 =
      2 * l / (1 - (p : R3) 2) := Real.sq_sqrt (by positivity)
  have he := sphere_equation p
  dsimp [south, radiusSq]
  simp only [mul_pow, neg_sq, hs]
  field_simp
  nlinarith [he]

lemma northInv_mem (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : northInvAmbient l z ∈ Metric.sphere (0 : R3) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hr := Real.sq_sqrt (show 0 ≤ 4 * l - radiusSq z by linarith)
  have hn := EuclideanSpace.real_norm_sq_eq (northInvAmbient l z)
  simp only [Fin.sum_univ_three, northInvAmbient, vec3_apply_zero,
    vec3_apply_one, vec3_apply_two, div_pow, mul_pow, hr] at hn
  have hh : ‖northInvAmbient l z‖ ^ 2 = 1 := by
    change ‖northInvAmbient l z‖ ^ 2 = _ at hn
    rw [hn]
    unfold radiusSq
    field_simp
    ring
  nlinarith [norm_nonneg (northInvAmbient l z)]

lemma sqrt_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (a * b) = a := by
  rw [← Real.sqrt_mul (div_nonneg ha hb.le)]
  have hh : a / b * (a * b) = a ^ 2 := by field_simp
  rw [hh, Real.sqrt_sq ha]

lemma north_left_inv (l : ℝ) (hl : 0 < l) (p : S2)
    (hp : -1 < (p : R3) 2) : northInvAmbient l (north l p) = p := by
  have hd : 0 < 1 + (p : R3) 2 := by linarith
  have hr := north_radius l hl p hp
  have hroot : Real.sqrt (2 * l / (1 + (p : R3) 2)) *
      Real.sqrt (4 * l - radiusSq (north l p)) = 2 * l := by
    rw [hr, show 4 * l - 2 * l * (1 - (p : R3) 2) =
      2 * l * (1 + (p : R3) 2) by ring]
    exact sqrt_pair (show 0 ≤ 2 * l by positivity) hd
  ext i
  fin_cases i
  · change Real.sqrt (2 * l / (1 + (p : R3) 2)) * (p : R3) 0 *
        Real.sqrt (4 * l - radiusSq (north l p)) / (2 * l) = (p : R3) 0
    rw [mul_assoc, mul_comm ((p : R3) 0), ← mul_assoc, hroot]
    field_simp
  · change Real.sqrt (2 * l / (1 + (p : R3) 2)) * (p : R3) 1 *
        Real.sqrt (4 * l - radiusSq (north l p)) / (2 * l) = (p : R3) 1
    rw [mul_assoc, mul_comm ((p : R3) 1), ← mul_assoc, hroot]
    field_simp
  · change 1 - radiusSq (north l p) / (2 * l) = (p : R3) 2
    rw [hr]
    field_simp
    ring

lemma northInv_height (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : -1 < northInvAmbient l z 2 := by
  change -1 < 1 - radiusSq z / (2 * l)
  have hh : radiusSq z / (2 * l) < 2 := (div_lt_iff₀ (by positivity)).2 (by linarith)
  linarith

lemma north_right_inv (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) :
    north l ⟨northInvAmbient l z, northInv_mem l hl z hz⟩ = z := by
  have hd : 0 < 1 + northInvAmbient l z 2 := by
    have := northInv_height l hl z hz; linarith
  have hc : 2 * l * (1 + northInvAmbient l z 2) = 4 * l - radiusSq z := by
    change 2 * l * (1 + (1 - radiusSq z / (2 * l))) = _
    field_simp
    ring
  have hroot := sqrt_pair (show 0 ≤ 2 * l by positivity) hd
  rw [hc] at hroot
  ext
  · change Real.sqrt (2 * l / (1 + northInvAmbient l z 2)) *
        (z.1 * Real.sqrt (4 * l - radiusSq z) / (2 * l)) = z.1
    calc
      _ = (Real.sqrt (2 * l / (1 + northInvAmbient l z 2)) *
        Real.sqrt (4 * l - radiusSq z)) * z.1 / (2 * l) := by ring
      _ = z.1 := by rw [hroot]; field_simp
  · change Real.sqrt (2 * l / (1 + northInvAmbient l z 2)) *
        (z.2 * Real.sqrt (4 * l - radiusSq z) / (2 * l)) = z.2
    calc
      _ = (Real.sqrt (2 * l / (1 + northInvAmbient l z 2)) *
        Real.sqrt (4 * l - radiusSq z)) * z.2 / (2 * l) := by ring
      _ = z.2 := by rw [hroot]; field_simp

lemma smooth_north (l : ℝ) (hl : 0 < l) (p : S2) (hp : -1 < (p : R3) 2) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, Plane) ∞ (north l) p := by
  let f : R3 → Plane := fun q =>
    (Real.sqrt (2 * l / (1 + q 2)) * q 0,
      Real.sqrt (2 * l / (1 + q 2)) * q 1)
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun q : R3 => q i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hd : 0 < 1 + (p : R3) 2 := by linarith
  have hf : ContDiffAt ℝ ∞ f (p : R3) := by
    have hdiv : ContDiffAt ℝ ∞ (fun q : R3 => 2 * l / (1 + q 2)) (p : R3) :=
      contDiffAt_const.div (contDiffAt_const.add (hc 2).contDiffAt) hd.ne'
    have hs := hdiv.sqrt (show 2 * l / (1 + (p : R3) 2) ≠ 0 by positivity)
    exact (hs.mul (hc 0).contDiffAt).prodMk (hs.mul (hc 1).contDiffAt)
  exact hf.contMDiffAt.comp p ((contMDiff_coe_sphere (E := R3) (n := 2)).contMDiffAt)

lemma smooth_northInvAmbient (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : ContDiffAt ℝ ∞ (northInvAmbient l) z := by
  have hr : ContDiff ℝ ∞ radiusSq := contDiff_fst.pow 2 |>.add (contDiff_snd.pow 2)
  have hs : ContDiffAt ℝ ∞ (fun y : Plane => Real.sqrt (4 * l - radiusSq y)) z :=
    (contDiffAt_const.sub hr.contDiffAt).sqrt (by linarith)
  rw [contDiffAt_piLp]
  intro i
  fin_cases i
  · exact (contDiffAt_fst.mul hs).div contDiffAt_const (mul_pos (by norm_num) hl).ne'
  · exact (contDiffAt_snd.mul hs).div_const (2 * l)
  · exact contDiffAt_const.sub (hr.contDiffAt.div_const (2 * l))

lemma northPole_mem : vec3 0 0 1 ∈ Metric.sphere (0 : R3) 1 := by
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three]

def northInv (l : ℝ) (hl : 0 < l) (z : Plane) : S2 :=
  if hz : radiusSq z < 4 * l then ⟨northInvAmbient l z, northInv_mem l hl z hz⟩
  else ⟨vec3 0 0 1, northPole_mem⟩

@[simp] lemma northInv_val (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : (northInv l hl z : R3) = northInvAmbient l z := by
  simp only [northInv, dite_eq_left hz]

lemma capDomain_open (l : ℝ) : IsOpen {z : Plane | radiusSq z < 4 * l} := by
  exact isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const

def capDomain (l : ℝ) : TopologicalSpace.Opens Plane := ⟨_, capDomain_open l⟩

lemma smooth_northInv (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : ContMDiffAt 𝓘(ℝ, Plane) (𝓡 2) ∞ (northInv l hl) z := by
  let g : capDomain l → R3 := fun y => northInvAmbient l y
  have hg : ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, R3) ∞ g := by
    intro y
    exact (smooth_northInvAmbient l hl y y.2).contMDiffAt.comp y
      contMDiff_subtype_val.contMDiffAt
  have hm : ∀ y : capDomain l, g y ∈ Metric.sphere (0 : R3) 1 :=
    fun y => northInv_mem l hl y y.2
  have ht := hg.codRestrict_sphere (n := 2) hm
  have heq : (Set.codRestrict g _ hm : capDomain l → S2) =
      fun y : capDomain l => northInv l hl y := by
    funext y
    apply Subtype.ext
    exact (northInv_val l hl y y.2).symm
  rw [heq] at ht
  exact contMDiffAt_subtype_iff.mp (ht (⟨z,hz⟩ : capDomain l))

lemma north_map (l : ℝ) (hl : 0 < l) (p : S2) (hp : -1 < (p : R3) 2) :
    radiusSq (north l p) < 4 * l := by
  rw [north_radius l hl p hp]
  nlinarith

def northChart (l : ℝ) (hl : 0 < l) : OpenPartialHomeomorph S2 Plane where
  toFun := north l
  invFun := northInv l hl
  source := {p | -1 < (p : R3) 2}
  target := {z | radiusSq z < 4 * l}
  map_source' := fun _ hp => north_map l hl _ hp
  map_target' := fun _ hz => by
    change -1 < (northInv l hl _ : R3) 2
    rw [northInv_val l hl _ hz]
    exact northInv_height l hl _ hz
  left_inv' := fun _ hp => by
    apply Subtype.ext
    rw [northInv_val l hl _ (north_map l hl _ hp)]
    exact north_left_inv l hl _ hp
  right_inv' := fun z hz => by
    change radiusSq z < 4 * l at hz
    simp only [northInv, dite_eq_left hz]
    exact north_right_inv l hl _ hz
  open_source := isOpen_lt continuous_const
    ((EuclideanSpace.proj 2).continuous.comp continuous_subtype_val)
  open_target := capDomain_open l
  continuousOn_toFun := fun p hp => (smooth_north l hl p hp).continuousAt.continuousWithinAt
  continuousOn_invFun := fun z hz => (smooth_northInv l hl z hz).continuousAt.continuousWithinAt

theorem north_chart (l : ℝ) (hl : 0 < l) :
    ∃ e : OpenPartialHomeomorph S2 Plane,
      (∀ p, e p = north l p) ∧
      e.source = {p : S2 | -1 < (p : R3) 2} ∧
      e.target = {z | radiusSq z < 4 * l} ∧
      (∀ z ∈ e.target, (e.symm z : R3) = northInvAmbient l z) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, Plane) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, Plane) (𝓡 2) ∞ e.symm e.target := by
  refine ⟨northChart l hl, fun _ => rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact fun z hz => northInv_val l hl z hz
  · exact fun p hp => (smooth_north l hl p hp).contMDiffWithinAt
  · exact fun z hz => (smooth_northInv l hl z hz).contMDiffWithinAt

theorem caps_disjoint (l : ℝ) (hl : 25 / 2 < l) :
    Disjoint {p : S2 | -1 < (p : R3) 2 ∧ radiusSq (north l p) < 25}
      {p : S2 | (p : R3) 2 < 1 ∧ radiusSq (south l p) < 25} := by
  refine Set.disjoint_left.mpr fun p hp hq => ?_
  have hl0 : 0 < l := by linarith
  rcases hp with ⟨hp,hpr⟩
  rcases hq with ⟨hq,hqr⟩
  rw [north_radius l hl0 p hp] at hpr
  rw [south_radius l hl0 p hq] at hqr
  nlinarith

def radialL (z : Plane) : Plane →L[ℝ] ℝ :=
  z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] lemma radialL_apply (z v : Plane) : radialL z v = z.1 * v.1 + z.2 * v.2 := rfl

lemma radiusSq_deriv (z : Plane) : HasFDerivAt radiusSq (2 • radialL z) z := by
  convert (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).pow 2 |>.add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2) using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  simp [radialL]
  ring

lemma div_const_deriv {f : Plane → ℝ} {f' : Plane →L[ℝ] ℝ} {z : Plane}
    (hf : HasFDerivAt f f' z) (c : ℝ) :
    HasFDerivAt (fun y => f y / c) (c⁻¹ • f') z := by
  simpa only [Pi.smul_def, div_eq_mul_inv, smul_eq_mul, mul_comm] using hf.const_smul c⁻¹

def vecL (a b c : Plane →L[ℝ] ℝ) : Plane →L[ℝ] R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![a,b,c])

@[simp] lemma vecL_apply (a b c : Plane →L[ℝ] ℝ) (v : Plane) :
    vecL a b c v = vec3 (a v) (b v) (c v) := by
  ext i
  fin_cases i <;> rfl

lemma vec3_deriv {a b c : Plane → ℝ} {a' b' c' : Plane →L[ℝ] ℝ} {z : Plane}
    (ha : HasFDerivAt a a' z) (hb : HasFDerivAt b b' z) (hc : HasFDerivAt c c' z) :
    HasFDerivAt (fun y => vec3 (a y) (b y) (c y)) (vecL a' b' c') z := by
  have hpi : HasFDerivAt (fun y => ![a y, b y, c y])
      (ContinuousLinearMap.pi ![a',b',c']) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp z hpi

def northJac (l : ℝ) (z : Plane) : Plane →L[ℝ] R3 :=
  let s := Real.sqrt (4 * l - radiusSq z)
  vecL ((s / (2 * l)) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (z.1 / (2 * l * s)) • radialL z)
    ((s / (2 * l)) • ContinuousLinearMap.snd ℝ ℝ ℝ -
    (z.2 / (2 * l * s)) • radialL z)
    ((-1 / l) • radialL z)

theorem northInv_deriv (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) : HasFDerivAt (northInvAmbient l) (northJac l z) z := by
  let s := Real.sqrt (4 * l - radiusSq z)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hsd : HasFDerivAt (fun y => Real.sqrt (4 * l - radiusSq y))
      ((-1 / s) • radialL z) z := by
    convert ((hasFDerivAt_const (4 * l) z).sub (radiusSq_deriv z)).sqrt
      (show 4 * l - radiusSq z ≠ 0 by linarith) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply, sub_apply, zero_apply, smul_eq_mul, nsmul_eq_mul]
    change (-1 / s) * radialL z v = (1 / (2 * s)) * (0 - 2 * radialL z v)
    ring
  have hx := div_const_deriv (hasFDerivAt_fst.mul hsd) (2 * l)
  have hy := div_const_deriv (hasFDerivAt_snd.mul hsd) (2 * l)
  have hh := (hasFDerivAt_const (1 : ℝ) z).sub (div_const_deriv (radiusSq_deriv z) (2 * l))
  convert vec3_deriv hx hy hh using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;>
    simp [northJac, vecL_apply, s,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] <;>
    field_simp <;> ring

lemma area_northJac (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) (v w : Plane) :
    l * standardArea (northInvAmbient l z) (northJac l z v) (northJac l z w) =
      v.1 * w.2 - v.2 * w.1 := by
  have hd : 0 < 4 * l - radiusSq z := by linarith
  let s := Real.sqrt (4 * l - radiusSq z)
  have hs : s ^ 2 = 4 * l - radiusSq z := Real.sq_sqrt hd.le
  have hs0 : Real.sqrt (4 * l - radiusSq z) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  simp only [standardArea, northInvAmbient, northJac, vecL_apply,
    vec3_apply_zero, vec3_apply_one, vec3_apply_two,
    sub_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', radialL_apply,
    smul_eq_mul]
  change _ = v.1 * w.2 - v.2 * w.1
  generalize hst : Real.sqrt (4 * l - radiusSq z) = t at *
  dsimp only [s] at hs
  rw [hst] at hs
  field_simp
  ring_nf
  simp only [show t ^ 4 = (t ^ 2) ^ 2 by ring, hs, radiusSq]
  ring

def flipL : R3 →L[ℝ] R3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![EuclideanSpace.proj 0, -EuclideanSpace.proj 1,
      -EuclideanSpace.proj 2])

lemma flipL_apply (p : R3) : flipL p = vec3 (p 0) (-p 1) (-p 2) := by
  ext i
  fin_cases i <;> rfl

lemma flipL_involutive (p : R3) : flipL (flipL p) = p := by
  simp only [flipL_apply, vec3_apply_zero, vec3_apply_one, vec3_apply_two, neg_neg]
  ext i
  fin_cases i <;> rfl

lemma flipL_mem (p : S2) : flipL (p : R3) ∈ Metric.sphere (0 : R3) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hn := EuclideanSpace.real_norm_sq_eq (flipL (p : R3))
  simp only [flipL_apply, Fin.sum_univ_three, vec3_apply_zero, vec3_apply_one,
    vec3_apply_two, neg_sq] at hn
  have he := sphere_equation p
  have hpos := norm_nonneg (flipL (p : R3))
  rw [flipL_apply] at hpos ⊢
  nlinarith

def flipS (p : S2) : S2 := ⟨flipL p, flipL_mem p⟩

lemma flipS_involutive (p : S2) : flipS (flipS p) = p := by
  apply Subtype.ext
  exact flipL_involutive p

lemma flipS_smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ flipS := by
  exact (flipL.contMDiff.comp (contMDiff_coe_sphere (E := R3) (n := 2))).codRestrict_sphere
    (n := 2) flipL_mem

lemma north_flipS (l : ℝ) (p : S2) : north l (flipS p) = south l p := by
  simp [north, south, flipS, flipL_apply, sub_eq_add_neg]

lemma flip_northInv (l : ℝ) (z : Plane) :
    flipL (northInvAmbient l z) = southInvAmbient l z := by
  ext i
  fin_cases i <;> simp [flipL_apply, northInvAmbient, southInvAmbient] <;> ring

lemma smooth_south (l : ℝ) (hl : 0 < l) (p : S2) (hp : (p : R3) 2 < 1) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, Plane) ∞ (south l) p := by
  have hp' : -1 < (flipS p : R3) 2 := by
    simp only [flipS, flipL_apply, vec3_apply_two]
    linarith
  simpa only [Function.comp_def, north_flipS] using
    (smooth_north l hl (flipS p) hp').comp p (flipS_smooth.contMDiffAt)

lemma south_map (l : ℝ) (hl : 0 < l) (p : S2) (hp : (p : R3) 2 < 1) :
    radiusSq (south l p) < 4 * l := by
  rw [south_radius l hl p hp]
  nlinarith

def southChart (l : ℝ) (hl : 0 < l) : OpenPartialHomeomorph S2 Plane where
  toFun := south l
  invFun := flipS ∘ northInv l hl
  source := {p | (p : R3) 2 < 1}
  target := {z | radiusSq z < 4 * l}
  map_source' := fun _ hp => south_map l hl _ hp
  map_target' := fun z hz => by
    change radiusSq z < 4 * l at hz
    change (flipL (northInv l hl z : R3)) 2 < 1
    rw [northInv_val l hl z hz, flip_northInv]
    change -1 + radiusSq z / (2 * l) < 1
    have : radiusSq z / (2 * l) < 2 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
    linarith
  left_inv' := fun p hp => by
    change (p : R3) 2 < 1 at hp
    change flipS (northInv l hl (south l p)) = p
    rw [← north_flipS]
    have hp' : -1 < (flipS p : R3) 2 := by
      simp only [flipS, flipL_apply, vec3_apply_two]
      linarith
    have he : northInv l hl (north l (flipS p)) = flipS p := by
      apply Subtype.ext
      rw [northInv_val l hl _ (north_map l hl _ hp')]
      exact north_left_inv l hl _ hp'
    rw [he, flipS_involutive]
  right_inv' := fun z hz => by
    change south l (flipS (northInv l hl z)) = z
    rw [← north_flipS, flipS_involutive]
    exact (northChart l hl).right_inv hz
  open_source := isOpen_lt
    ((EuclideanSpace.proj 2).continuous.comp continuous_subtype_val) continuous_const
  open_target := capDomain_open l
  continuousOn_toFun := fun p hp => (smooth_south l hl p hp).continuousAt.continuousWithinAt
  continuousOn_invFun := fun z hz =>
    ((flipS_smooth.contMDiffAt).comp z (smooth_northInv l hl z hz)).continuousAt.continuousWithinAt

theorem south_chart (l : ℝ) (hl : 0 < l) :
    ∃ e : OpenPartialHomeomorph S2 Plane,
      (∀ p, e p = south l p) ∧
      e.source = {p : S2 | (p : R3) 2 < 1} ∧
      e.target = {z | radiusSq z < 4 * l} ∧
      (∀ z ∈ e.target, (e.symm z : R3) = southInvAmbient l z) ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, Plane) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, Plane) (𝓡 2) ∞ e.symm e.target := by
  refine ⟨southChart l hl, fun _ => rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro z hz
    change flipL (northInv l hl z : R3) = southInvAmbient l z
    rw [northInv_val l hl z hz, flip_northInv]
  · exact fun p hp => (smooth_south l hl p hp).contMDiffWithinAt
  · exact fun z hz => ((flipS_smooth.contMDiffAt).comp z
      (smooth_northInv l hl z hz)).contMDiffWithinAt

lemma standardArea_flip (p v w : R3) :
    standardArea (flipL p) (flipL v) (flipL w) = standardArea p v w := by
  simp only [standardArea, flipL_apply, vec3_apply_zero, vec3_apply_one, vec3_apply_two]
  ring

lemma southInv_deriv (l : ℝ) (hl : 0 < l) (z : Plane) (hz : radiusSq z < 4 * l) :
    HasFDerivAt (southInvAmbient l) (flipL.comp (northJac l z)) z := by
  simpa only [Function.comp_def, flip_northInv] using
    flipL.hasFDerivAt.comp z (northInv_deriv l hl z hz)

theorem cap_area (l : ℝ) (hl : 0 < l) (z : Plane)
    (hz : radiusSq z < 4 * l) (v w : Plane) :
    l * standardArea (northInvAmbient l z)
      (fderiv ℝ (northInvAmbient l) z v) (fderiv ℝ (northInvAmbient l) z w) =
      v.1 * w.2 - v.2 * w.1 ∧
    l * standardArea (southInvAmbient l z)
      (fderiv ℝ (southInvAmbient l) z v) (fderiv ℝ (southInvAmbient l) z w) =
      v.1 * w.2 - v.2 * w.1 := by
  rw [(northInv_deriv l hl z hz).fderiv, (southInv_deriv l hl z hz).fderiv]
  constructor
  · exact area_northJac l hl z hz v w
  · rw [← flip_northInv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, standardArea_flip]
    exact area_northJac l hl z hz v w

end
end MorseArnold.SphereCaps

end

end OAI
