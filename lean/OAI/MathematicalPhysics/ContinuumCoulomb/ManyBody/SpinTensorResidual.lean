import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorTotalReplacement
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullSpinTensorCoefficients
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealSpinOrbitals

namespace OAI

/-! Tensor residual bounds in the full physical spin measure, with the exact
mass of the weak-H1 finite tensor state as normalization. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem spinTensorResidual_L2_bound {n : ℕ} {α : Type*} [Fintype α]
    (v r : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (c : (Fin (n+1) → α) → ℂ) :
    (∫ x, ‖tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
      (fun a => Coulomb.flatSpinOrbital (r a)) c x‖^2
      ∂(Measure.pi fun _ : Fin (n+1) => Coulomb.spinSpaceMeasure)) ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖Coulomb.flatSpinOrbital (r a) x‖^2 ∂Coulomb.spinSpaceMeasure)*
        Coulomb.mass (finiteTensorState v hv hL2 hpartial c) := by
  have hflat (a b : α) :
      (∫ x, star (Coulomb.flatSpinOrbital (v a) x)*Coulomb.flatSpinOrbital (v b) x
        ∂Coulomb.spinSpaceMeasure) = if a=b then (1:ℂ) else 0 := by
    rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
    exact ho a b
  rw [finiteTensorState_mass v hv hL2 hpartial ho c]
  exact tensorTotalReplacement_L2_bound _ _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a))
    (fun a => Coulomb.flatSpinOrbital_memLp (r a) (hr a)) hflat c

theorem flatRealSpinOrbital_norm_sq (f : Position → ℝ) (hf : MemLp f 2) (σ : Fin 2) :
    (∫ x, ‖Coulomb.flatSpinOrbital (realSpinOrbital f σ) x‖^2 ∂Coulomb.spinSpaceMeasure) =
      ∫ x, f x^2 := by
  have h := Coulomb.flatSpinOrbital_inner (realSpinOrbital f σ) (realSpinOrbital f σ)
    (realSpinOrbital_memLp f hf σ) (realSpinOrbital_memLp f hf σ)
  have hn (z : ℂ) : star z*z = ((‖z‖^2:ℝ):ℂ) := by
    simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' z
  rw [realSpinOrbital_inner] at h
  simp_rw [hn] at h
  rw [integral_complex_ofReal] at h
  simpa only [ite_true,← pow_two,Complex.ofReal_inj] using h

end ContinuumCoulomb

end

end OAI
