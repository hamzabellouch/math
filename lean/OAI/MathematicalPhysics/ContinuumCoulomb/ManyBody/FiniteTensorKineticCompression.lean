import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockResidualIntegral
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorDiagonal

namespace OAI

/-! The actual differential residual identifies the finite tensor kinetic
and bounded-potential form with its CAR matrix. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_residual_compression {n Q : ℕ}
    (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) :
    (∑ s, ∫ x, star ((finiteTensorState v hv hL2 hpartial c).value s x)*
      finiteTensorResidualValue v r c s x) =
      Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)) := by
  have he := spinConfiguration_complex_integral
    (fun s x => star ((finiteTensorState v hv hL2 hpartial c).value s x)*
      finiteTensorResidualValue v r c s x)
    (fun s => ((finiteTensorState v hv hL2 hpartial c).value_L2 s).star.integrable_mul
      (finiteTensorResidualValue_memLp v r hL2 hr c s))
  rw [← he]
  have hp : (fun z : Fin (n+1) → Fin 2 × (Fin 3 → ℝ) =>
      star ((finiteTensorState v hv hL2 hpartial c).value ((Coulomb.spinCubeEquiv (n+1)) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv (n+1)) z).2))*
      finiteTensorResidualValue v r c ((Coulomb.spinCubeEquiv (n+1)) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv (n+1)) z).2)) =
      fun z => star (FockSlaterTensor.tensorValue (fun a => Coulomb.flatSpinOrbital (v a)) c z)*
        tensorTotalReplacement (fun a => Coulomb.flatSpinOrbital (v a))
          (fun a => Coulomb.flatSpinOrbital (r a)) c z := by
    funext z
    rw [finiteTensorResidualValue_eq_flat,spinConfigurationPoint_coordinates]
    rfl
  rw [hp]
  apply FockResidualIntegral.tensorValue_residual_integral _ _
    (fun a => Coulomb.flatSpinOrbital_memLp (v a) (hL2 a))
    (fun a => Coulomb.flatSpinOrbital_memLp (r a) (hr a)) _ c c hc hc
  intro a b
  rw [Coulomb.flatSpinOrbital_inner _ _ (hL2 a) (hL2 b)]
  exact ho a b

theorem finiteTensorState_bounded_compression (hdensity : PublishedSobolevSmoothDensity)
    {n Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B : ℝ)
    (hB : ∀ x : Configuration (n+1), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (c : Laughlin.State (n+1) Q) (hc : Laughlin.Antisymmetric c) :
    let p := finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c
    boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+1:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+1) Q c)
        (HubbardGlobal.oneBodyOperator (fun a b =>
          ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
            ∂Coulomb.spinSpaceMeasure)
          (Laughlin.Fock.normalizedTensorExterior (n+1) Q c))).re := by
  let hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s) :=
    fun a s => (hv a s).of_le (by norm_num)
  let p := finiteTensorState v hv₁ hL2 hpartial c
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
  have hswap : (∑ s, ∫ x, star (R s x)*p.value s x).re =
      (∑ s, ∫ x, star (p.value s x)*R s x).re := by
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hi : Integrable (fun x => star (R s x)*p.value s x) :=
      (hR s).star.integrable_mul (p.value_L2 s)
    have hj : Integrable (fun x => star (p.value s x)*R s x) :=
      (p.value_L2 s).star.integrable_mul (hR s)
    calc
      _ = ∫ x, (star (R s x)*p.value s x).re := (integral_re hi).symm
      _ = ∫ x, (star (p.value s x)*R s x).re := by
        congr 1
        funext x
        simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
        ring
      _ = _ := integral_re hj
  change boundedPotentialForm W p-(n+1:ℝ)*E*Coulomb.mass p = _
  rw [hre,hswap,finiteTensorState_residual_compression v r hv₁ hL2 hpartial hr ho c hc]

end ContinuumCoulomb

end

end OAI
