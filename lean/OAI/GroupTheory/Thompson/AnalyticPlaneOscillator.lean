import OAI.GroupTheory.Thompson.AnalyticModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# The Euclidean planar oscillator

The ordinary sine/cosine circle and its tangent have unit Euclidean norm.
The derivative of the tangent is the negative circle vector. The mean value
inequality therefore gives Lipschitz constant one for both functions, and a
quadratic first-order remainder estimate with constant one.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

def planeWave (z : ℝ) : Plane := !₂[Real.cos z, Real.sin z]

def planeDeriv (z : ℝ) : Plane := !₂[-Real.sin z, Real.cos z]

@[simp] theorem planeWave_norm (z : ℝ) : ‖planeWave z‖ = 1 := by
  simp [planeWave, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq]

@[simp] theorem planeDeriv_norm (z : ℝ) : ‖planeDeriv z‖ = 1 := by
  simp [planeDeriv, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs, Real.sin_sq_add_cos_sq]

theorem planeWave_inner_planeDeriv (z : ℝ) :
    ⟪planeWave z, planeDeriv z⟫_ℝ = 0 := by
  simp [planeWave, planeDeriv, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, mul_comm]

theorem planeWave_inner (s t : ℝ) :
    ⟪planeWave s, planeWave t⟫_ℝ = Real.cos (t - s) := by
  simp [planeWave, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    Real.cos_sub]

private theorem hasDerivAt_planePair {f g : ℝ → ℝ} {f' g' z : ℝ}
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (fun x => (!₂[f x, g x] : Plane)) (!₂[f', g'] : Plane) z := by
  have h : HasDerivAt (fun x => (![f x, g x] : Fin 2 → ℝ)) ![f', g'] z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hf
    · simpa using hg
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt z h

theorem hasDerivAt_planeWave (z : ℝ) :
    HasDerivAt planeWave (planeDeriv z) z :=
  hasDerivAt_planePair (Real.hasDerivAt_cos z) (Real.hasDerivAt_sin z)

theorem hasDerivAt_planeDeriv (z : ℝ) :
    HasDerivAt planeDeriv (-planeWave z) z := by
  have h := hasDerivAt_planePair (Real.hasDerivAt_sin z).neg (Real.hasDerivAt_cos z)
  have he : (!₂[-Real.cos z, -Real.sin z] : Plane) = -planeWave z := by
    ext i
    fin_cases i <;> simp [planeWave]
  rw [he] at h
  exact h

theorem continuous_planeWave : Continuous planeWave :=
  Differentiable.continuous (fun z => (hasDerivAt_planeWave z).differentiableAt)

theorem continuous_planeDeriv : Continuous planeDeriv :=
  Differentiable.continuous (fun z => (hasDerivAt_planeDeriv z).differentiableAt)

theorem planeWave_sub_norm_le (s t : ℝ) :
    ‖planeWave s - planeWave t‖ ≤ |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := planeWave) (f' := planeDeriv) (C := 1)
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) =>
      (hasDerivAt_planeWave x).hasDerivWithinAt)
    (fun x _ => le_of_eq (planeDeriv_norm x)) convex_univ (mem_univ t) (mem_univ s)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem planeDeriv_sub_norm_le (s t : ℝ) :
    ‖planeDeriv s - planeDeriv t‖ ≤ |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := planeDeriv) (f' := fun x => -planeWave x) (C := 1)
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) =>
      (hasDerivAt_planeDeriv x).hasDerivWithinAt)
    (fun x _ => by simp) convex_univ (mem_univ t) (mem_univ s)
  simpa only [one_mul, Real.norm_eq_abs] using h

theorem planeWave_remainder (s t : ℝ) :
    ‖planeWave t - planeWave s - (t - s) • planeDeriv s‖ ≤ |t - s| ^ 2 := by
  have hd (x : ℝ) :
      HasDerivAt (fun y => planeWave y - planeWave s - (y - s) • planeDeriv s)
        (planeDeriv x - planeDeriv s) x := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_planeWave x).sub_const (planeWave s)).fun_sub
        (((hasDerivAt_id x).sub_const s).smul_const (planeDeriv s))
  have hbound (x : ℝ) (hx : x ∈ segment ℝ s t) :
      ‖planeDeriv x - planeDeriv s‖ ≤ |t - s| := by
    apply (planeDeriv_sub_norm_le x s).trans
    simpa only [Real.norm_eq_abs] using norm_sub_le_of_mem_segment hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ segment ℝ s t) => (hd x).hasDerivWithinAt)
    hbound (convex_segment s t) (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
  simpa only [sub_self, zero_smul, sub_zero, Real.norm_eq_abs, pow_two] using h

end ThompsonNonamenability.Analytic

end

end OAI
