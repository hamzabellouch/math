import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorCross

namespace OAI

/-! The differential residual also controls the compressed diagonal energy.
This estimate retains polynomial dependence on the number of particles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem graphBoundedCross_self {n : ℕ} (V : Configuration n → ℝ)
    (hV : Continuous V) (B : ℝ) (hB : ∀ x, |V x| ≤ B) (u : Coulomb.H1Vector n) :
    graphBoundedCross (BoundedPotential.operator V hV B hB)
      (h1Coordinates u) (h1Coordinates u) = boundedPotentialForm V u := by
  rw [boundedPotentialForm_eq_graph V hV B hB]
  simp only [graphBoundedCross,graphBoundedForm,graphKinetic,real_inner_self_eq_norm_sq]

theorem finiteTensorState_diagonal_square_bound (hdensity : PublishedSobolevSmoothDensity)
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
    (c : (Fin (n+1) → α) → ℂ) :
    let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
    (boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+1:ℝ)*E*Coulomb.mass p)^2 ≤
      (n+1:ℝ)^2*(∑ a, ∫ x, ‖Coulomb.flatSpinOrbital (r a) x‖^2 ∂Coulomb.spinSpaceMeasure)*
        Coulomb.mass p*Coulomb.mass p := by
  let p : Coulomb.H1Vector (n+1) := finiteTensorState (n := n+1) v hv₁ hL2 hpartial c
  let W : Configuration (n+1) → ℝ := fun x => ∑ i, V (Coulomb.position x i)
  have hW : Continuous W := continuous_finsetSum _ (fun i _ => hV.comp (Coulomb.positionCLM i).continuous)
  let R := finiteTensorResidualValue v r c
  have hR := finiteTensorResidualValue_memLp v r hL2 hr c
  have hid := classical_residual_pairing hdensity p p W hW B ((n+1:ℝ)*E) hB R hR
    (finiteTensorState_value_C2 v hv hL2 hpartial c)
    (finiteTensorState_gradient_classical v hv₁ hL2 hpartial c)
    (fun s x => by simpa only [Nat.cast_add,Nat.cast_one] using
      finiteTensorState_operator_residual v r hv hL2 hpartial V E heq c s x)
  have hself : (inner ℂ p.toHilbert p.toHilbert).re = Coulomb.mass p := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) p.toHilbert).symm.trans
      (Coulomb.H1Vector.toHilbert_norm_sq p)
  have hre := congrArg Complex.re hid
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hself,← graphBoundedCross_eq_re,graphBoundedCross_self] at hre
  have hnorm := spinTensorResidual_L2_bound v r hv₁ hL2 hpartial hr ho c
  rw [← finiteTensorResidualValue_norm v r hL2 hr c] at hnorm
  have hb := (residual_integral_square_bound p R hR).trans
    (mul_le_mul_of_nonneg_right hnorm (Coulomb.mass_nonneg p))
  change (boundedPotentialForm W p-(n+1:ℝ)*E*Coulomb.mass p)^2 ≤ _
  rw [hre]
  apply le_trans _ hb
  rw [complex_norm_sq_parts]
  nlinarith only [sq_nonneg ((∑ s, ∫ x, star (R s x)*p.value s x).im)]

end ContinuumCoulomb

end

end OAI
