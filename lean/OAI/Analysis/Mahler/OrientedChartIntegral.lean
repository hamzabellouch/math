import OAI.Analysis.Mahler.ChartStokes
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- Orientation of a real Jacobian. Its value at zero is immaterial for
change of variables; genuine local diffeomorphisms have nonzero Jacobian. -/
def jacobianOrientation (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

lemma jacobianOrientation_mul (a : ℝ) : jacobianOrientation a * a = |a| := by
  unfold jacobianOrientation
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

/-- A top alternating form transforms by the determinant in the ordered
standard coordinate basis. -/
theorem topForm_apply_linear {d : ℕ}
    (A : (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ) (L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    A (fun i => L (coordinateBasis d i)) = L.det * A (coordinateBasis d) := by
  let b := Pi.basisFun ℝ (Fin d)
  have he := congrArg (fun f : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ =>
    f (fun i => L (b i))) (A.toAlternatingMap.eq_smul_basis_det b)
  have hd : b.det (fun i => L (b i)) = L.det := by
    change b.det (L.toLinearMap ∘ b) = L.det
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at he
  rw [hd] at he
  have hb : (b : Fin d → (Fin d → ℝ)) = coordinateBasis d := by
    ext i j
    simp [b, coordinateBasis]
  rw [← hb]
  exact he.trans (mul_comm _ _)

/-- Actual Lebesgue change of variables for an oriented top form. The
orientation factor converts the signed determinant to the positive Jacobian. -/
theorem integral_image_topForm {d : ℕ} {s : Set (Fin d → ℝ)}
    (φ : (Fin d → ℝ) → (Fin d → ℝ))
    (A : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ)
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, DifferentiableAt ℝ φ x) (hinj : InjOn φ s) :
    (∫ x in φ '' s, A x (coordinateBasis d)) =
      ∫ y in s, jacobianOrientation (fderiv ℝ φ y).det *
        A (φ y) (fun i => fderiv ℝ φ y (coordinateBasis d i)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun x hx => (hφ x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  apply integral_congr_ae
  filter_upwards with y
  rw [topForm_apply_linear, ← mul_assoc, jacobianOrientation_mul]
  rfl

/-- The actual exterior derivative on a C2 coordinate chart, with the
Jacobian orientation made explicit in the volume integral. -/
theorem integral_image_extDeriv {n : ℕ} {s : Set (Fin (n+1) → ℝ)}
    (φ : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hs : MeasurableSet s) (hφ : ∀ x ∈ s, ContDiffAt ℝ 2 φ x)
    (hinj : InjOn φ s) (hω : ∀ x ∈ s, DifferentiableAt ℝ ω (φ x)) :
    (∫ x in φ '' s, extDeriv ω x (coordinateBasis (n+1))) =
      ∫ y in s, jacobianOrientation (fderiv ℝ φ y).det *
        extDeriv (pullbackForm φ ω) y (coordinateBasis (n+1)) := by
  rw [integral_image_topForm φ (extDeriv ω) hs
    (fun x hx => (hφ x hx).differentiableAt (by simp)) hinj]
  apply setIntegral_congr_fun hs
  intro y hy
  dsimp only
  unfold pullbackForm
  rw [extDeriv_pullback (hω y hy) (hφ y hy) (by simp)]
  rfl

/-- At a nonzero Jacobian, orientation is locally constant. -/
theorem jacobianOrientation_eventuallyEq {E : Type*} [TopologicalSpace E]
    {f : E → ℝ} {x : E} (hf : ContinuousAt f x) (hx : f x ≠ 0) :
    (fun y => jacobianOrientation (f y)) =ᶠ[𝓝 x] (fun _ => jacobianOrientation (f x)) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hn : ∀ᶠ y in 𝓝 x, f y < 0 := hf.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hn] with y hy
    simp [jacobianOrientation, not_le.mpr hy, not_le.mpr hneg]
  · have hn : ∀ᶠ y in 𝓝 x, 0 < f y := hf.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hn] with y hy
    simp [jacobianOrientation, hy.le, hpos.le]

end MahlerStokes

end

end OAI
