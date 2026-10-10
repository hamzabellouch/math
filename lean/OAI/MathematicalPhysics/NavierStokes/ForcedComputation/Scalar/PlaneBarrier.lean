import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMaximumCompact
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarComparison

namespace OAI

/-! A quadratic barrier for bounded whole-plane drift. It supplies strict
comparison without requiring compact support of the diffusing scalar. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

def planeBarrierSquare (x : Plane) : ℝ := 1 + (x 0) ^ 2 + (x 1) ^ 2

theorem planeBarrierSquare_smooth : ContDiff ℝ ∞ planeBarrierSquare := by
  unfold planeBarrierSquare
  fun_prop

theorem planeBarrierSquare_one_le (x : Plane) : 1 ≤ planeBarrierSquare x := by
  unfold planeBarrierSquare
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

theorem planeBarrierSquare_fderiv (x v : Plane) :
    fderiv ℝ planeBarrierSquare x v = 2 * x 0 * v 0 + 2 * x 1 * v 1 := by
  have hd := (((hasFDerivAt_apply (𝕜 := ℝ) 0 x).pow 2).const_add 1).add
    ((hasFDerivAt_apply (𝕜 := ℝ) 1 x).pow 2)
  change HasFDerivAt planeBarrierSquare _ x at hd
  rw [hd.fderiv]
  simp

theorem planeBarrierSquare_spatialD (j : Fin 2) :
    spatialD j planeBarrierSquare = fun x => 2 * x j := by
  funext x
  rw [spatialD, planeBarrierSquare_fderiv]
  fin_cases j <;> simp [PlanarHamiltonian.basis]

theorem planeBarrierSquare_laplacian (x : Plane) :
    scalarLaplacian planeBarrierSquare x = 4 := by
  have hd (j : Fin 2) : spatialD j (spatialD j planeBarrierSquare) x = 2 := by
    rw [planeBarrierSquare_spatialD]
    have hh := (hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul 2
    simp [spatialD, hh.fderiv, PlanarHamiltonian.basis]
  norm_num [scalarLaplacian, hd]

theorem planeBarrierSquare_generator (ν : ℝ) (a : Plane → Plane) (x : Plane) :
    scalarGenerator ν a planeBarrierSquare x =
      4 * ν - (2 * x 0 * a x 0 + 2 * x 1 * a x 1) := by
  rw [scalarGenerator, planeBarrierSquare_laplacian, planeBarrierSquare_fderiv]
  ring

theorem planeBarrierSquare_generator_bound {ν A : ℝ} (hν : 0 ≤ ν) (_hA : 0 ≤ A)
    (a : Plane → Plane) (ha : ∀ x, ‖a x‖ ≤ A) (x : Plane) :
    scalarGenerator ν a planeBarrierSquare x + planeBarrierSquare x ≤
      (4 * ν + 2 * A ^ 2 + 2) * planeBarrierSquare x := by
  have hac (j : Fin 2) : |a x j| ≤ A := by
    have hnorm : |a x j| ≤ ‖a x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (a x) j)
    exact hnorm.trans (ha x)
  have hs (j : Fin 2) : -(2 * x j * a x j) ≤ (x j) ^ 2 + A ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hac j)
    have hsquare : (a x j) ^ 2 ≤ A ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi)
        (show 0 ≤ A + a x j by linarith)]
    nlinarith [sq_nonneg (x j + a x j)]
  have hsum : 0 ≤ (x 0) ^ 2 + (x 1) ^ 2 := by positivity
  have hcoef : 0 ≤ 4 * ν + 2 * A ^ 2 := by positivity
  rw [planeBarrierSquare_generator]
  unfold planeBarrierSquare
  nlinarith [hs 0, hs 1, mul_nonneg hcoef hsum]

theorem spatialD_const_mul {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (j : Fin 2) :
    spatialD j (fun x => c * f x) = fun x => c * spatialD j f x := by
  funext x
  simp only [spatialD, fderiv_const_mul (hf.differentiable (by simp) x) c,
    smul_apply, smul_eq_mul]

theorem scalarGenerator_const_mul {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (ν c : ℝ) (a : Plane → Plane) (x : Plane) :
    scalarGenerator ν a (fun y => c * f y) x = c * scalarGenerator ν a f x := by
  have hl : scalarLaplacian (fun y => c * f y) x = c * scalarLaplacian f x := by
    simp only [scalarLaplacian, spatialD_const_mul hf,
      spatialD_const_mul (spatialD_smooth _ hf), Finset.mul_sum]
  simp only [scalarGenerator, hl, fderiv_const_mul (hf.differentiable (by simp) x) c,
    smul_apply, smul_eq_mul]
  ring

theorem quadratic_barrier_positive_compact {w : ℝ → Plane → ℝ} {T B ε : ℝ}
    (hε : 0 < ε) (hb : ∀ t ∈ Icc 0 T, ∀ x, w t x ≤ B)
    (c : ℝ → ℝ) (hc : ∀ t ∈ Icc 0 T, 1 ≤ c t) :
    ∃ K : Set Plane, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x,
      0 < w t x - ε * c t * planeBarrierSquare x → x ∈ K := by
  let R := |B| / ε + 1
  have hdiv : 0 ≤ |B| / ε := div_nonneg (abs_nonneg _) hε.le
  have hR : 0 < R := by dsimp [R]; linarith
  have hR₁ : 1 ≤ R := by dsimp [R]; linarith
  have hmul : ε * R = |B| + ε := by
    dsimp [R]
    field_simp [hε.ne']
  have hBR : B < ε * R ^ 2 := by
    have hsq : R ≤ R ^ 2 := by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hR₁)]
    have hle := mul_le_mul_of_nonneg_left hsq hε.le
    nlinarith [le_abs_self B]
  refine ⟨Icc (fun _ : Fin 2 => -R) (fun _ => R), isCompact_Icc, ?_⟩
  intro t ht x hx
  have hp : 0 ≤ planeBarrierSquare x := (by norm_num : (0 : ℝ) ≤ 1).trans
    (planeBarrierSquare_one_le x)
  have hcoef : ε ≤ ε * c t := by nlinarith [hc t ht]
  have hφ : ε * planeBarrierSquare x < B := by
    have hm := mul_le_mul_of_nonneg_right hcoef hp
    linarith [hb t ht x]
  have hj (j : Fin 2) : |x j| < R := by
    have hsq : (x j) ^ 2 ≤ planeBarrierSquare x := by
      fin_cases j
      · change (x 0) ^ 2 ≤ 1 + (x 0) ^ 2 + (x 1) ^ 2
        nlinarith [sq_nonneg (x 1)]
      · change (x 1) ^ 2 ≤ 1 + (x 0) ^ 2 + (x 1) ^ 2
        nlinarith [sq_nonneg (x 0)]
    have hεsq : ε * (x j) ^ 2 < ε * R ^ 2 :=
      ((mul_le_mul_of_nonneg_left hsq hε.le).trans_lt hφ).trans hBR
    exact abs_lt_of_sq_lt_sq ((mul_lt_mul_iff_right₀ hε).mp hεsq) hR.le
  exact ⟨fun j => (abs_lt.mp (hj j)).1.le, fun j => (abs_lt.mp (hj j)).2.le⟩

end ForcedComputation.VelocityDetector

end

end OAI
