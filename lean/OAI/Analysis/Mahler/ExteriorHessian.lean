import OAI.Analysis.Mahler.ExteriorFlux
import OAI.Analysis.Mahler.OpenHessian

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- Actual mixed derivatives expanded in the real second Fréchet derivative. -/
lemma mixed_second_real [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v w : E} (hu : ContDiffAt ℝ 2 u x) :
    dbar (fun y => dz u y v) x w =
      (fderiv ℝ (fderiv ℝ u) x w v - I * fderiv ℝ (fderiv ℝ u) x w (I • v) +
        I * fderiv ℝ (fderiv ℝ u) x (I • w) v +
        fderiv ℝ (fderiv ℝ u) x (I • w) (I • v)) / 4 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hiv := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (I • v) x)
  have hdz := (hv.sub (hiv.const_mul I)).mul_const (2 : ℂ)⁻¹
  change HasFDerivAt (fun y => dz u y v) _ x at hdz
  rw [dbar, hdz.fderiv]
  simp
  linear_combination -(fderiv ℝ (fderiv ℝ u) x (I • w) (I • v) / 4) * I_mul_I

/-- The exterior derivative of the d^c one-form is exactly the
antisymmetrized mixed Hessian, with coefficient i/2. -/
theorem extDeriv_dc_mixed {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) (v w : E) :
    extDeriv (oneForm (dcLinear u)) x ![v, w] =
      (I / 2) * (dbar (fun y => dz u y v) x w - dbar (fun y => dz u y w) x v) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hdc (a b : E) : fderiv ℝ (fun y => dcLinear u y a) x b =
      (-1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) x b (I • a) := by
    have he : (fun y => dcLinear u y a) =
        (fun y => (-1 / 4 : ℂ) * fderiv ℝ u y (I • a)) := by
      funext y
      simp [dcLinear]
    rw [he]
    have hh := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (I • a) x)).const_mul (-1 / 4 : ℂ)
    rw [hh.fderiv]
    simp
  rw [extDeriv_oneForm (differentiableAt_dcLinear hu), hdc, hdc,
    mixed_second_real hu, mixed_second_real hu]
  have hs := hu.isSymmSndFDerivAt (by simp)
  rw [hs.eq w v, hs.eq (I • w) v, hs.eq (I • v) w, hs.eq (I • w) (I • v)]
  linear_combination -((fderiv ℝ (fderiv ℝ u) x v (I • w) -
    fderiv ℝ (fderiv ℝ u) x w (I • v)) / 4) * I_mul_I

/-- The exterior two-form identity, with no added regularity. -/
theorem extDeriv_dc_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (v w : E) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![v, w] =
      (I / 2) *
        (logKernel (fun j => f j x) (fun j => fderiv ℂ (f j) x w)
          (fun j => fderiv ℂ (f j) x v) -
         logKernel (fun j => f j x) (fun j => fderiv ℂ (f j) x v)
          (fun j => fderiv ℂ (f j) x w)) := by
  rw [extDeriv_dc_mixed (contDiffAt_logTau_of_open hU hx hf ht)]
  rw [mixed_logTau_of_open hU hx hf ht, mixed_logTau_of_open hU hx hf ht]
  rfl

end Mahler

end OAI
