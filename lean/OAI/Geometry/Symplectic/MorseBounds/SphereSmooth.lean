import OAI.Geometry.Symplectic.MorseBounds.SphereCaps

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SphereCaps
open scoped ContDiff Manifold
open Set
noncomputable section
local instance sphereSmoothFinrank : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp [R3]⟩

def capHeight (l : ℝ) : ℝ := 1 - 25 / (2 * l)
def capStep (l h : ℝ) : ℝ := Real.smoothTransition ((h + capHeight l) / (2 * capHeight l))
def angularSpeed (l eps s h : ℝ) : ℝ :=
  if s = -1 then (2 * Real.pi - eps) + (2 * eps - 2 * Real.pi) * capStep l h
  else eps + (2 * Real.pi - 2 * eps) * capStep l h

def rotateAmbient (t : ℝ) (p : R3) : R3 :=
  vec3 (Real.cos t * p 0 - Real.sin t * p 1)
    (Real.sin t * p 0 + Real.cos t * p 1) (p 2)
def rotatePlane (t : ℝ) (z : Plane) : Plane :=
  (Real.cos t * z.1 - Real.sin t * z.2, Real.sin t * z.1 + Real.cos t * z.2)

lemma rotateAmbient_height (t : ℝ) (p : R3) : rotateAmbient t p 2 = p 2 := rfl

lemma rotateAmbient_sq (t : ℝ) (p : R3) :
    (rotateAmbient t p) 0 ^ 2 + (rotateAmbient t p) 1 ^ 2 + (rotateAmbient t p) 2 ^ 2 =
      p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  simp only [rotateAmbient, vec3_apply_zero, vec3_apply_one, vec3_apply_two]
  calc
    _ = (p 0 ^ 2 + p 1 ^ 2) * (Real.sin t ^ 2 + Real.cos t ^ 2) + p 2 ^ 2 := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem rotate_mem (t : ℝ) (p : S2) : rotateAmbient t p ∈ Metric.sphere (0 : R3) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hn := EuclideanSpace.real_norm_sq_eq (rotateAmbient t p)
  simp only [Fin.sum_univ_three] at hn
  rw [rotateAmbient_sq] at hn
  have he := sphere_equation p
  have hp := norm_nonneg (rotateAmbient t p)
  nlinarith

def rotate (t : ℝ) (p : S2) : S2 := ⟨rotateAmbient t p, rotate_mem t p⟩
def sphereFlow (l eps s t : ℝ) (p : S2) : S2 :=
  rotate (t * angularSpeed l eps s ((p : R3) 2)) p

def poleSet : Set S2 := {p | (p : R3) 0 = 0 ∧ (p : R3) 1 = 0}
def sphereHamiltonian (l eps s h : ℝ) : ℝ :=
  l * ∫ x in (0 : ℝ)..h, angularSpeed l eps s x

lemma capStep_smooth (l : ℝ) : ContDiff ℝ ∞ (capStep l) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)

lemma angularSpeed_smooth (l eps s : ℝ) : ContDiff ℝ ∞ (angularSpeed l eps s) := by
  unfold angularSpeed
  split_ifs <;> exact contDiff_const.add (contDiff_const.mul (capStep_smooth l))

lemma angularSpeed_bounds (l eps s : ℝ) (hepspi : eps < Real.pi) (h : ℝ) :
    eps ≤ angularSpeed l eps s h ∧ angularSpeed l eps s h ≤ 2 * Real.pi - eps := by
  have h0 := Real.smoothTransition.nonneg ((h + capHeight l) / (2 * capHeight l))
  have h1 := Real.smoothTransition.le_one ((h + capHeight l) / (2 * capHeight l))
  unfold angularSpeed capStep
  split_ifs <;> constructor <;> nlinarith

lemma capHeight_pos (l : ℝ) (hl : 25 / 2 < l) : 0 < capHeight l := by
  have hl0 : 0 < l := by linarith
  have : 25 / (2 * l) < 1 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  dsimp [capHeight]
  linarith

lemma capStep_north (l : ℝ) (hl : 25 / 2 < l) (h : ℝ) (hh : capHeight l ≤ h) :
    capStep l h = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (mul_pos (by norm_num) (capHeight_pos l hl))).mpr
  linarith

lemma capStep_south (l : ℝ) (hl : 25 / 2 < l) (h : ℝ) (hh : h ≤ -capHeight l) :
    capStep l h = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  positivity [capHeight_pos l hl]

theorem speed_properties (l eps s : ℝ) (hl : 25 / 2 < l)
    (_heps : 0 < eps) (hepspi : eps < Real.pi) (_hs : s = -1 ∨ s = 1) :
    ContDiff ℝ ∞ (angularSpeed l eps s) ∧
    (∀ h, eps ≤ angularSpeed l eps s h ∧ angularSpeed l eps s h ≤ 2 * Real.pi - eps) ∧
    (∀ h, capHeight l ≤ h → angularSpeed l eps s h =
      if s = -1 then eps else 2 * Real.pi - eps) ∧
    (∀ h, h ≤ -capHeight l → angularSpeed l eps s h =
      if s = -1 then 2 * Real.pi - eps else eps) := by
  refine ⟨angularSpeed_smooth l eps s, angularSpeed_bounds l eps s hepspi, ?_, ?_⟩
  · intro h hh
    unfold angularSpeed
    rw [capStep_north l hl h hh]
    split_ifs <;> ring
  · intro h hh
    unfold angularSpeed
    rw [capStep_south l hl h hh]
    split_ifs <;> ring

lemma rotateAmbient_zero (p : R3) : rotateAmbient 0 p = p := by
  ext i
  fin_cases i <;> simp [rotateAmbient]

lemma rotateAmbient_add (t u : ℝ) (p : R3) :
    rotateAmbient (t + u) p = rotateAmbient t (rotateAmbient u p) := by
  ext i
  fin_cases i <;> simp [rotateAmbient, Real.sin_add, Real.cos_add] <;> ring

lemma rotate_zero (p : S2) : rotate 0 p = p := by
  apply Subtype.ext
  exact rotateAmbient_zero p

lemma rotate_add (t u : ℝ) (p : S2) : rotate (t + u) p = rotate t (rotate u p) := by
  apply Subtype.ext
  exact rotateAmbient_add t u p

@[simp] lemma rotate_height (t : ℝ) (p : S2) : (rotate t p : R3) 2 = (p : R3) 2 := rfl

theorem sphereFlow_laws (l eps s : ℝ) :
    (∀ p, sphereFlow l eps s 0 p = p) ∧
    (∀ t u p, sphereFlow l eps s (t + u) p = sphereFlow l eps s t (sphereFlow l eps s u p)) := by
  constructor
  · intro p
    simp [sphereFlow, rotate_zero]
  · intro t u p
    simp only [sphereFlow, rotate_height, add_mul, rotate_add]

lemma rotateAmbient_smooth : ContDiff ℝ ∞ (fun q : ℝ × R3 => rotateAmbient q.1 q.2) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × R3 => q.2 i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (contDiff_fst.cos.mul (hc 0)).sub (contDiff_fst.sin.mul (hc 1))
  · exact (contDiff_fst.sin.mul (hc 0)).add (contDiff_fst.cos.mul (hc 1))
  · exact hc 2

lemma rotate_smooth : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
    (fun q : ℝ × S2 => rotate q.1 q.2) := by
  have hcoe : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ, R3) ∞
      (fun q : ℝ × S2 => (q.2 : R3)) :=
    (contMDiff_coe_sphere (E := R3) (n := 2)).comp contMDiff_snd
  have hprod : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × R3) ∞
      (fun q : ℝ × S2 => (q.1, (q.2 : R3))) :=
    (contMDiff_prod_module_iff _).mpr ⟨contMDiff_fst, hcoe⟩
  have ha := rotateAmbient_smooth.contMDiff.comp hprod
  exact ha.codRestrict_sphere (n := 2) (fun q => rotate_mem q.1 q.2)

lemma height_smooth : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : S2 => (p : R3) 2) := by
  have hc : ContDiff ℝ ∞ (fun q : R3 => q 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact hc.contMDiff.comp (contMDiff_coe_sphere (E := R3) (n := 2))

lemma sphereFlow_time_smooth (l eps s : ℝ) :
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
      (fun q : ℝ × S2 => q.1 * angularSpeed l eps s ((q.2 : R3) 2)) := by
  have hh : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
      (fun q : ℝ × S2 => (q.2 : R3) 2) := height_smooth.comp contMDiff_snd
  have hspeed : ContMDiff (𝓘(ℝ).prod (𝓡 2)) 𝓘(ℝ) ∞
      (fun q : ℝ × S2 => angularSpeed l eps s ((q.2 : R3) 2)) :=
    (angularSpeed_smooth l eps s).contMDiff.comp hh
  exact contMDiff_fst.mul hspeed

theorem sphereFlow_smooth (l eps s : ℝ) :
    ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × S2 => sphereFlow l eps s q.1 q.2) := by
  have hp : ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓘(ℝ).prod (𝓡 2)) ∞
      (fun q : ℝ × S2 => (q.1 * angularSpeed l eps s ((q.2 : R3) 2), q.2)) :=
    (sphereFlow_time_smooth l eps s).prodMk contMDiff_snd
  change ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
    ((fun q : ℝ × S2 => rotate q.1 q.2) ∘
      (fun q : ℝ × S2 => (q.1 * angularSpeed l eps s ((q.2 : R3) 2), q.2)))
  exact rotate_smooth.comp hp

lemma rotate_fixed_iff (t : ℝ) (ht : 0 < t) (ht2 : t < 2 * Real.pi) (p : S2) :
    rotate t p = p ↔ p ∈ poleSet := by
  constructor
  · intro he
    have hc : Real.cos t ≠ 1 := by
      intro h
      have hz := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) ht2).mp h
      linarith
    have hd : 0 < (Real.cos t - 1) ^ 2 + Real.sin t ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hc)) (sq_nonneg _)
    have h0 := congrArg (fun q : S2 => (q : R3) 0) he
    have h1 := congrArg (fun q : S2 => (q : R3) 1) he
    change Real.cos t * (p : R3) 0 - Real.sin t * (p : R3) 1 = (p : R3) 0 at h0
    change Real.sin t * (p : R3) 0 + Real.cos t * (p : R3) 1 = (p : R3) 1 at h1
    have ha : ((Real.cos t - 1) ^ 2 + Real.sin t ^ 2) * (p : R3) 0 = 0 := by
      linear_combination (Real.cos t - 1) * h0 + Real.sin t * h1
    have hb : ((Real.cos t - 1) ^ 2 + Real.sin t ^ 2) * (p : R3) 1 = 0 := by
      linear_combination -Real.sin t * h0 + (Real.cos t - 1) * h1
    exact ⟨(mul_eq_zero.mp ha).resolve_left hd.ne', (mul_eq_zero.mp hb).resolve_left hd.ne'⟩
  · rintro ⟨h0,h1⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [rotate, rotateAmbient, h0, h1]

theorem sphereFlow_fixed (l eps s : ℝ) (heps : 0 < eps)
    (hepspi : eps < Real.pi) (p : S2) :
    sphereFlow l eps s 1 p = p ↔ p ∈ poleSet := by
  have hb := angularSpeed_bounds l eps s hepspi ((p : R3) 2)
  simp only [sphereFlow, one_mul]
  exact rotate_fixed_iff _ (by linarith) (by linarith) p

lemma north_rotate (l t : ℝ) (p : S2) :
    north l (rotate t p) = rotatePlane t (north l p) := by
  ext <;> simp [north, rotate, rotateAmbient, rotatePlane] <;> ring

lemma south_rotate (l t : ℝ) (p : S2) :
    south l (rotate t p) = rotatePlane (-t) (south l p) := by
  ext <;> simp [south, rotate, rotateAmbient, rotatePlane] <;> ring

lemma rotatePlane_two_pi_sub (t : ℝ) (z : Plane) :
    rotatePlane (2 * Real.pi - t) z = rotatePlane (-t) z := by
  simp [rotatePlane, Real.sin_two_pi_sub, Real.cos_two_pi_sub]

lemma rotatePlane_neg_two_pi_sub (t : ℝ) (z : Plane) :
    rotatePlane (-(2 * Real.pi - t)) z = rotatePlane t z := by
  simp [rotatePlane]

lemma north_cap_height (l : ℝ) (hl : 25 / 2 < l) (p : S2)
    (hp : -1 < (p : R3) 2) (hcap : radiusSq (north l p) < 25) :
    capHeight l ≤ (p : R3) 2 := by
  have hl0 : 0 < l := by linarith
  rw [north_radius l hl0 p hp] at hcap
  have hh : 1 - (p : R3) 2 < 25 / (2 * l) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  dsimp [capHeight]
  linarith

lemma south_cap_height (l : ℝ) (hl : 25 / 2 < l) (p : S2)
    (hp : (p : R3) 2 < 1) (hcap : radiusSq (south l p) < 25) :
    (p : R3) 2 ≤ -capHeight l := by
  have hl0 : 0 < l := by linarith
  rw [south_radius l hl0 p hp] at hcap
  have hh : 1 + (p : R3) 2 < 25 / (2 * l) :=
    (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  dsimp [capHeight]
  linarith

theorem sphereFlow_north_endpoint (l eps s : ℝ) (hl : 25 / 2 < l)
    (hs : s = -1 ∨ s = 1) (p : S2)
    (hp : -1 < (p : R3) 2) (hcap : radiusSq (north l p) < 25) :
    north l (sphereFlow l eps s 1 p) = rotatePlane (-s * eps) (north l p) := by
  have hstep := capStep_north l hl _ (north_cap_height l hl p hp hcap)
  simp only [sphereFlow, one_mul, north_rotate]
  rcases hs with rfl | rfl
  · simp only [angularSpeed, ite_true, hstep, mul_one]
    congr 1; ring
  · simp only [angularSpeed, show (1:ℝ) ≠ -1 by norm_num, ite_false, hstep, mul_one]
    have he : eps + (2 * Real.pi - 2 * eps) = 2 * Real.pi - eps := by ring
    rw [he, rotatePlane_two_pi_sub]
    simp

theorem sphereFlow_south_endpoint (l eps s : ℝ) (hl : 25 / 2 < l)
    (hs : s = -1 ∨ s = 1) (p : S2)
    (hp : (p : R3) 2 < 1) (hcap : radiusSq (south l p) < 25) :
    south l (sphereFlow l eps s 1 p) = rotatePlane (-s * eps) (south l p) := by
  have hstep := capStep_south l hl _ (south_cap_height l hl p hp hcap)
  simp only [sphereFlow, one_mul, south_rotate]
  rcases hs with rfl | rfl
  · simp only [angularSpeed, ite_true, hstep, mul_zero, add_zero]
    rw [rotatePlane_neg_two_pi_sub]
    simp
  · simp only [angularSpeed, show (1:ℝ) ≠ -1 by norm_num, ite_false, hstep, mul_zero, add_zero]
    simp

lemma sphereHamiltonian_deriv (l eps s h : ℝ) :
    HasDerivAt (sphereHamiltonian l eps s) (l * angularSpeed l eps s h) h := by
  have hc := (angularSpeed_smooth l eps s).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 h)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_mul l

lemma sphereHamiltonian_smooth (l eps s : ℝ) : ContDiff ℝ ∞ (sphereHamiltonian l eps s) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun h => (sphereHamiltonian_deriv l eps s h).differentiableAt, ?_⟩
  have he : deriv (sphereHamiltonian l eps s) = fun h => l * angularSpeed l eps s h :=
    funext fun h => (sphereHamiltonian_deriv l eps s h).deriv
  rw [he]
  exact contDiff_const.mul (angularSpeed_smooth l eps s)

theorem sphere_hamiltonian_equation (l eps s : ℝ) (p : S2) (v : R3)
    (hv : (p : R3) 0 * v 0 + (p : R3) 1 * v 1 + (p : R3) 2 * v 2 = 0) :
    l * standardArea p
      (vec3 (-angularSpeed l eps s ((p : R3) 2) * (p : R3) 1)
        (angularSpeed l eps s ((p : R3) 2) * (p : R3) 0) 0) v =
    deriv (sphereHamiltonian l eps s) ((p : R3) 2) * v 2 := by
  rw [(sphereHamiltonian_deriv l eps s ((p : R3) 2)).deriv]
  simp only [standardArea, vec3_apply_zero, vec3_apply_one, vec3_apply_two]
  have he := sphere_equation p
  linear_combination l * angularSpeed l eps s ((p : R3) 2) * v 2 * he -
    l * angularSpeed l eps s ((p : R3) 2) * (p : R3) 2 * hv

end
end MorseArnold.SphereCaps

end

end OAI
