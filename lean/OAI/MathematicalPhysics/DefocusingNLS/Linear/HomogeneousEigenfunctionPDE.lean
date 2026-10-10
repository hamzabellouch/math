import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousClassicalLinearization
import Mathlib.Analysis.Calculus.FDeriv.Star

namespace OAI

/-! # The two classical channels of an actual semigroup eigenvector

The complexification used by the spectral argument has two physical channels.
An eigenvector of the actual evolution satisfies their coupled elliptic equations;
the required C² regularity follows from membership in Y with k > 8.
-/

open Set
open scoped Laplacian ZeroAtInfty ComplexConjugate NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem laplacian_channel_add (u v : E → ℂ) (c : ℂ) (x : E)
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    Δ (fun y => u y + c * v y) x = Δ u x + c * Δ v x := by
  have h := hu.laplacian_add (hv.const_smul c)
  calc
    Δ (fun y => u y + c * v y) x = Δ u x + Δ (fun y => c • v y) x := h
    _ = Δ u x + c * Δ v x := by
      congr 1
      exact InnerProductSpace.laplacian_smul c hv

private theorem fderiv_channel_add (u v : E → ℂ) (c : ℂ) (x : E)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => u y + c * v y) x x =
      fderiv ℝ u x x + c * fderiv ℝ v x x := by
  change (fderiv ℝ (u + c • v) x) x = _
  rw [fderiv_add hu (hv.const_smul c), fderiv_const_smul hv c]
  rfl

private theorem laplacian_channel_star (u : E → ℂ) (x : E) :
    Δ (fun y => star (u y)) x = star (Δ u x) := by
  exact congrFun (InnerProductSpace.laplacian_CLE_comp_left
    (f := u) (l := (starL' ℝ : ℂ ≃L[ℝ] ℂ))) x

private theorem fderiv_channel_star (u : E → ℂ) (x : E) :
    fderiv ℝ (fun y => star (u y)) x x = star (fderiv ℝ u x x) := by
  rw [fderiv_star]
  rfl

/-- A semigroup eigenvector has the actual two-channel classical PDE, with
coefficients obtained from the derivative of the odd-power nonlinearity. -/
theorem homogeneous_eigenvector_classical_channels (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q : HomogeneousY a k) (lam : ℂ) (w : HomogeneousY a k × HomogeneousY a k)
    (hw : ∀ t : ℝ≥0, homogeneousComplexLinearizedStep a b k ha ha1 hk m q t w =
      Complex.exp (((t : ℝ) : ℂ) * lam) • w) :
    let P := fun f : HomogeneousY a k =>
      fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
    ContDiff ℝ 2 (P w.1) ∧ ContDiff ℝ 2 (P w.2) ∧
      ∀ x : E,
      (lam * P w.1 x = Complex.I * Δ (P w.1) x -
        (1 / 2 : ℂ) * fderiv ℝ (P w.1) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * P w.1 x - Complex.I *
          ((((m + 1 : ℕ) : ℂ) * P q x ^ m * star (P q x) ^ m) * P w.1 x +
            ((m : ℂ) * P q x ^ (m + 1) * star (P q x) ^ (m - 1)) * P w.2 x)) ∧
      (lam * P w.2 x = -Complex.I * Δ (P w.2) x -
        (1 / 2 : ℂ) * fderiv ℝ (P w.2) x x +
        (-(a : ℂ) - Complex.I * (b : ℂ)) * P w.2 x + Complex.I *
          (star (((m + 1 : ℕ) : ℂ) * P q x ^ m * star (P q x) ^ m) * P w.2 x +
            star ((m : ℂ) * P q x ^ (m + 1) * star (P q x) ^ (m - 1)) * P w.1 x)) := by
  dsimp only
  let P := fun f : HomogeneousY a k =>
    fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
  let X := homogeneousComplexReal a k ha ha1 hk
  let Y := homogeneousComplexImag a k ha ha1 hk
  let u := P (X w)
  let v := P (Y w)
  change ContDiff ℝ 2 (P w.1) ∧ ContDiff ℝ 2 (P w.2) ∧
      ∀ x : E,
      (lam * P w.1 x = Complex.I * Δ (P w.1) x -
        (1 / 2 : ℂ) * fderiv ℝ (P w.1) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * P w.1 x - Complex.I *
          ((((m + 1 : ℕ) : ℂ) * P q x ^ m * star (P q x) ^ m) * P w.1 x +
            ((m : ℂ) * P q x ^ (m + 1) * star (P q x) ^ (m - 1)) * P w.2 x)) ∧
      (lam * P w.2 x = -Complex.I * Δ (P w.2) x -
        (1 / 2 : ℂ) * fderiv ℝ (P w.2) x x +
        (-(a : ℂ) - Complex.I * (b : ℂ)) * P w.2 x + Complex.I *
          (star (((m + 1 : ℕ) : ℂ) * P q x ^ m * star (P q x) ^ m) * P w.2 x +
            star ((m : ℂ) * P q x ^ (m + 1) * star (P q x) ^ (m - 1)) * P w.1 x))
  have hP (f : HomogeneousY a k) : ContDiff ℝ 2 (P f) :=
    contDiff_homogeneousPhysical a k ha ha1 hk f
  refine ⟨hP w.1, hP w.2, ?_⟩
  have hfirst (z : HomogeneousY a k × HomogeneousY a k) :
      P z.1 = fun x => P (X z) x + Complex.I * P (Y z) x := by
    funext x
    have h := congrArg (fun f : HomogeneousY a k => P f x)
      (homogeneousComplexCoordinates_first a k ha ha1 hk z)
    simpa only [P, X, Y, map_add, map_smul, ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul] using h.symm
  have hsecond (z : HomogeneousY a k × HomogeneousY a k) :
      P z.2 = fun x => star (P (X z) x) + Complex.I * star (P (Y z) x) := by
    funext x
    have h := congrArg (fun f : HomogeneousY a k => P f x)
      (homogeneousComplexCoordinates_second a k ha ha1 hk z)
    simpa only [P, X, Y, map_add, map_smul, ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul,
      homogeneousConjugation_physical, starRingEnd_apply] using h.symm
  have hu := hP (X w)
  have hv := hP (Y w)
  obtain ⟨hX, hY⟩ := homogeneous_eigenvector_free_coordinates a b k ha ha1 hk m q lam w hw
  intro x
  have hx := homogeneousLinearized_domain_classical a b k ha ha1 hk m q
    (X w) (X (lam • w)) hX x
  have hy := homogeneousLinearized_domain_classical a b k ha ha1 hk m q
    (Y w) (Y (lam • w)) hY x
  change P (X (lam • w)) x = Complex.I * Δ u x -
    (1 / 2 : ℂ) * fderiv ℝ u x x + (-(a : ℂ) + Complex.I * (b : ℂ)) * u x -
      Complex.I * oddPowerDerivative m (P q x) (u x) at hx
  change P (Y (lam • w)) x = Complex.I * Δ v x -
    (1 / 2 : ℂ) * fderiv ℝ v x x + (-(a : ℂ) + Complex.I * (b : ℂ)) * v x -
      Complex.I * oddPowerDerivative m (P q x) (v x) at hy
  have hlam₁ : lam * P w.1 x =
      P (X (lam • w)) x + Complex.I * P (Y (lam • w)) x := by
    have h := congrFun (hfirst (lam • w)) x
    simpa only [P, Prod.smul_fst, map_smul, ZeroAtInftyContinuousMap.smul_apply,
      smul_eq_mul] using h
  have hlam₂ : lam * P w.2 x =
      star (P (X (lam • w)) x) + Complex.I * star (P (Y (lam • w)) x) := by
    have h := congrFun (hsecond (lam • w)) x
    simpa only [P, Prod.smul_snd, map_smul, ZeroAtInftyContinuousMap.smul_apply,
      smul_eq_mul] using h
  have hd₁ := fderiv_channel_add u v Complex.I x
    (hu.differentiable (by norm_num) x) (hv.differentiable (by norm_num) x)
  have hl₁ := laplacian_channel_add u v Complex.I x hu.contDiffAt hv.contDiffAt
  have hd₂ := fderiv_channel_add (fun y => star (u y)) (fun y => star (v y)) Complex.I x
    ((hu.differentiable (by norm_num) x).star)
    ((hv.differentiable (by norm_num) x).star)
  have hus : ContDiff ℝ 2 (fun y => star (u y)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hu
  have hvs : ContDiff ℝ 2 (fun y => star (v y)) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hv
  have hl₂ := laplacian_channel_add (fun y => star (u y)) (fun y => star (v y))
    Complex.I x hus.contDiffAt hvs.contDiffAt
  rw [fderiv_channel_star, fderiv_channel_star] at hd₂
  rw [laplacian_channel_star, laplacian_channel_star] at hl₂
  constructor
  · rw [hlam₁, hx, hy, hfirst w, hsecond w]
    rw [hl₁, hd₁]
    simp only [oddPowerDerivative, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul]
    ring
  · rw [hlam₂, hx, hy, hsecond w, hfirst w]
    rw [hl₂, hd₂]
    simp only [oddPowerDerivative, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
      star_add, star_sub, star_mul, star_star, star_neg, star_pow]
    simp only [Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
      map_div₀, map_ofNat, map_one]
    dsimp only [u, v]
    ring

end DefocusingNLS

end OAI
