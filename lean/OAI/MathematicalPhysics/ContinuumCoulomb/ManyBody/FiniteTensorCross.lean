import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorResidual
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ClassicalResidualPairing

namespace OAI

/-! The actual finite tensor subspace has a polynomial mixed one-body form
bound against its orthogonal complement. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_mixed_square_bound (hdensity : PublishedSobolevSmoothDensity)
    {n : ℕ} {α : Type*} [Fintype α] (v r : α → Position → Fin 2 → ℂ)
    (hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B : ℝ)
    (hB : ∀ x : Configuration (n+1), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : (Fin (n+1) → α) → ℂ) (w : Coulomb.H1Vector (n+1)) :
    let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
    let W : Configuration (n+1) → ℝ := fun x => ∑ i, V (Coulomb.position x i)
    let hW : Continuous W := continuous_finsetSum _ (fun i _ => hV.comp (Coulomb.positionCLM i).continuous)
    inner ℂ p.toHilbert w.toHilbert = 0 →
    (graphBoundedCross (BoundedPotential.operator W hW B hB) (h1Coordinates p) (h1Coordinates w))^2 ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖Coulomb.flatSpinOrbital (r a) x‖^2 ∂Coulomb.spinSpaceMeasure)*
        Coulomb.mass p*Coulomb.mass w := by
  let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
  let W : Configuration (n+1) → ℝ := fun x => ∑ i, V (Coulomb.position x i)
  have hW : Continuous W := continuous_finsetSum _ (fun i _ => hV.comp (Coulomb.positionCLM i).continuous)
  change inner ℂ p.toHilbert w.toHilbert = 0 →
    (graphBoundedCross (BoundedPotential.operator W hW B hB) (h1Coordinates p) (h1Coordinates w))^2 ≤ _
  intro horth
  let R := finiteTensorResidualValue v r c
  have hR := finiteTensorResidualValue_memLp v r hL2 hr c
  have hid := classical_residual_pairing hdensity p w W hW B ((n+1:ℝ)*E) hB R hR
    (finiteTensorState_value_C2 v hv hL2 hpartial c)
    (finiteTensorState_gradient_classical v hv₁ hL2 hpartial c)
    (fun s x => by simpa only [Nat.cast_add,Nat.cast_one] using
      finiteTensorState_operator_residual v r hv hL2 hpartial V E heq c s x)
  rw [horth,mul_zero,sub_zero] at hid
  have hnorm := spinTensorResidual_L2_bound v r hv₁
    hL2 hpartial hr ho c
  rw [← finiteTensorResidualValue_norm v r hL2 hr c] at hnorm
  have hb := residual_integral_square_bound w R hR
  have htotal := hb.trans (mul_le_mul_of_nonneg_right hnorm (Coulomb.mass_nonneg w))
  change (graphBoundedCross (BoundedPotential.operator W hW B hB) (h1Coordinates p) (h1Coordinates w))^2 ≤ _
  rw [graphBoundedCross_eq_re,hid]
  apply le_trans _ htotal
  rw [complex_norm_sq_parts]
  nlinarith only [sq_nonneg ((∑ s, ∫ x, star (R s x)*w.value s x).im)]

end ContinuumCoulomb

end

end OAI
