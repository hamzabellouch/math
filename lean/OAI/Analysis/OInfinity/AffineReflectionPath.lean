import OAI.Analysis.OInfinity.CancellationBandwidth

namespace OAI

/-! # An affine path for each finite reflection

A selfadjoint unitary has an explicit path in its two-dimensional linear
span with the unit. Unlike a general short path, this formula preserves
commutator control directly. The resulting joint-cycle path has controlled commutators.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def reflectionPhase (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

lemma reflectionPhase_norm (θ : ℝ) : ‖reflectionPhase θ‖ = 1 := by
  simpa only [reflectionPhase, mul_comm] using Complex.norm_exp_ofReal_mul_I θ

lemma reflectionPhase_star_mul (θ : ℝ) : star (reflectionPhase θ) * reflectionPhase θ = 1 := by
  simpa only [RCLike.star_def, reflectionPhase_norm, one_pow, Complex.ofReal_one] using
    Complex.conj_mul' (reflectionPhase θ)

lemma reflectionPhase_sub_norm_le (θ φ : ℝ) :
    ‖reflectionPhase θ - reflectionPhase φ‖ ≤ |θ - φ| := by
  have he : reflectionPhase θ - reflectionPhase φ =
      reflectionPhase φ * (reflectionPhase (θ - φ) - 1) := by
    unfold reflectionPhase
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [he, norm_mul, reflectionPhase_norm, one_mul]
  rw [reflectionPhase, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |Real.sin ((θ - φ) / 2)| ≤ 2 * |(θ - φ) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |θ - φ| := by rw [abs_div]; norm_num; ring

def reflectionProjection (h : E) : E := (2 : ℂ)⁻¹ • (1 - h)

lemma reflectionProjection_star (h : E) (hh : star h = h) :
    star (reflectionProjection h) = reflectionProjection h := by
  simp only [reflectionProjection, star_smul, star_inv₀, star_ofNat, star_sub, star_one, hh]

lemma reflectionProjection_sq (h : E) (hh : h * h = 1) :
    reflectionProjection h * reflectionProjection h = reflectionProjection h := by
  simp only [reflectionProjection, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, one_mul, mul_one, hh]
  module_nf

private lemma projection_phase_product (q : E) (hq : q * q = q) (a b : ℂ) :
    (1 + a • q) * (1 + b • q) = 1 + (a + b + a * b) • q := by
  simp only [add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, hq]
  module

private lemma projection_phase_mem (q : E) (hqs : star q = q) (hq : q * q = q)
    (z : ℂ) (hz : star z * z = 1) : (1 + (z - 1) • q) ∈ unitary E := by
  have hc : (star z - 1) + (z - 1) + (star z - 1) * (z - 1) = 0 := by
    calc
      _ = star z * z - 1 := by ring
      _ = 0 := by rw [hz, sub_self]
  have hc' : (z - 1) + (star z - 1) + (z - 1) * (star z - 1) = 0 := by
    calc
      _ = (star z - 1) + (z - 1) + (star z - 1) * (z - 1) := by ring
      _ = 0 := hc
  constructor
  · simp only [star_add, star_one, star_smul, hqs, star_sub, star_one]
    rw [projection_phase_product q hq, hc, zero_smul, add_zero]
  · simp only [star_add, star_one, star_smul, hqs, star_sub, star_one]
    rw [projection_phase_product q hq, hc', zero_smul, add_zero]

def affineReflection (h : E) (θ : ℝ) : E :=
  1 + (reflectionPhase θ - 1) • reflectionProjection h

lemma affineReflection_mem (h : unitary E) (hh : star (h : E) = h) (θ : ℝ) :
    affineReflection (h : E) θ ∈ unitary E := by
  have hh₂ : (h : E) * h = 1 := by simpa only [hh] using h.property.1
  exact projection_phase_mem _ (reflectionProjection_star (h : E) hh)
    (reflectionProjection_sq (h : E) hh₂) _ (reflectionPhase_star_mul θ)

lemma affineReflection_zero (h : E) : affineReflection h 0 = 1 := by
  simp only [affineReflection, reflectionPhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    sub_self, zero_smul, add_zero]

lemma affineReflection_pi (h : E) : affineReflection h Real.pi = h := by
  have hp : reflectionPhase Real.pi = -1 := by
    simpa only [reflectionPhase, mul_comm] using Complex.exp_pi_mul_I
  rw [affineReflection, hp, reflectionProjection, smul_smul]
  module_nf

lemma affineReflection_continuous (h : E) : Continuous (affineReflection h) := by
  unfold affineReflection reflectionPhase
  fun_prop

lemma affineReflection_sub_norm_le (h : unitary E) (hh : star (h : E) = h)
    (θ φ : ℝ) : ‖affineReflection (h : E) θ - affineReflection (h : E) φ‖ ≤ |θ - φ| := by
  have hh₂ : (h : E) * h = 1 := by simpa only [hh] using h.property.1
  have hq : ‖reflectionProjection (h : E)‖ ≤ 1 := IsStarProjection.norm_le _
    (isStarProjection_iff'.mpr ⟨reflectionProjection_sq (h : E) hh₂, reflectionProjection_star (h : E) hh⟩)
  have he : affineReflection (h : E) θ - affineReflection (h : E) φ =
      (reflectionPhase θ - reflectionPhase φ) • reflectionProjection (h : E) := by
    unfold affineReflection
    module
  rw [he, norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hq).trans (reflectionPhase_sub_norm_le θ φ)

lemma affineReflection_commutator_bound (h : E) (θ : ℝ) (x : E) :
    ‖affineReflection (h : E) θ * x - x * affineReflection (h : E) θ‖ ≤ ‖h * x - x * h‖ := by
  have he : affineReflection (h : E) θ * x - x * affineReflection (h : E) θ =
      ((1 - reflectionPhase θ) / 2) • (h * x - x * h) := by
    simp only [affineReflection, reflectionProjection, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub]
    module
  have hz : ‖1 - reflectionPhase θ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one, reflectionPhase_norm]; norm_num)
  have hc : ‖(1 - reflectionPhase θ) / 2‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    linarith
  rw [he, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

/-- This path has an explicit affine formula and retains every commutator
bound of the reflection. Its speed is at most π. -/
def affineReflectionPath (h : unitary E) (hh : star (h : E) = h) : Path (1 : unitary E) h where
  toFun t := ⟨affineReflection (h : E) (Real.pi * (t : ℝ)), affineReflection_mem h hh _⟩
  continuous_toFun := Continuous.subtype_mk
    ((affineReflection_continuous (h : E)).comp (continuous_const.mul continuous_subtype_val)) _
  source' := by
    apply Subtype.ext
    change affineReflection (h : E) (Real.pi * 0) = 1
    simpa only [mul_zero] using affineReflection_zero (h : E)
  target' := by
    apply Subtype.ext
    change affineReflection (h : E) (Real.pi * 1) = (h : E)
    simpa only [mul_one] using affineReflection_pi (h : E)

lemma affineReflectionPath_sub_norm_le (h : unitary E) (hh : star (h : E) = h)
    (s t : unitInterval) :
    ‖(affineReflectionPath h hh s : E) - affineReflectionPath h hh t‖ ≤
      Real.pi * |(s : ℝ) - t| := by
  change ‖affineReflection (h : E) (Real.pi * (s : ℝ)) - affineReflection (h : E) (Real.pi * (t : ℝ))‖ ≤ _
  exact (affineReflection_sub_norm_le h hh _ _).trans_eq (by
    rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos])

lemma affineReflectionPath_commutator_bound (h : unitary E) (hh : star (h : E) = h)
    (t : unitInterval) (x : E) :
    ‖(affineReflectionPath h hh t : E) * x - x * affineReflectionPath h hh t‖ ≤
      ‖(h : E) * x - x * h‖ := affineReflection_commutator_bound _ _ _

end WeakPureInfiniteness

end

end OAI
