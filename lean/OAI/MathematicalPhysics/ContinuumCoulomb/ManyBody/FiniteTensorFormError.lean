import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorFormCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockEnergyError

namespace OAI

/-! The actual finite continuum form inherits the polynomial CAR coefficient
error bound, with no dependence on the exponentially large Fock dimension. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
namespace HubbardGlobal

theorem oneBodyOperator_smul {Q : ℕ} (z : ℂ) (K : Fin (Q+1) → Fin (Q+1) → ℂ) :
    oneBodyOperator (fun a b => z*K a b) = z • oneBodyOperator K := by
  simp only [oneBodyOperator,smul_smul,Finset.smul_sum]

theorem twoBodyOperator_smul {Q : ℕ} (z : ℂ)
    (W : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ) :
    twoBodyOperator (fun a b c d => z*W a b c d) = z • twoBodyOperator W := by
  simp only [twoBodyOperator,smul_smul,Finset.smul_sum,mul_assoc,mul_comm]

end HubbardGlobal

def nuclearFormIntegrable {n : ℕ} (F : Position → ℝ) (p : Coulomb.H1Vector n) : Prop :=
  ∀ s i, Integrable (fun x => F (Coulomb.position x i)*‖p.value s x‖^2)

section FormApproximation

variable (hdensity : PublishedSobolevSmoothDensity)

variable {n Q : ℕ}

variable (v r : Fin (Q+1) → Position → Fin 2 → ℂ)

variable (hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))

variable (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))

variable (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)

variable (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)

variable (hr : ∀ a s, MemLp (fun x => r a x s) 2)

variable (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)

variable (V : Position → ℝ)

variable (hV : Continuous V)

variable (E B t : ℝ)

variable (hB : ∀ x : Configuration (n+2), |∑ i, V (Coulomb.position x i)| ≤ B)

variable (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)

variable (F : Position → ℝ)

variable (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
      Coulomb.spinSpaceMeasure)

variable (hW : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))

variable (c : Laughlin.State (n+2) Q)

variable (hc : Laughlin.Antisymmetric c)

variable (hI : nuclearFormIntegrable F (finiteTensorState (n := n+2) v hv₁ hL2 hpartial c))

variable (scale ε η : ℝ)

variable (K : Fin (Q+1) → Fin (Q+1) → ℂ)

variable (W : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ)

variable (hK : ∀ a b, ‖(scale:ℂ)*(flatResidualMatrix v r a b+flatNuclearMatrix v F a b)-K a b‖ ≤ ε)

variable (hWerror : ∀ a b c d, ‖(scale*t:ℂ)*flatCoulombTensor v a b c d-W a b c d‖ ≤ η)

include hdensity hv hr ho hV hB heq hN hW hc hI hK hWerror

theorem finiteTensorState_form_approximation :
    let p := finiteTensorState (n := n+2) v hv₁ hL2 hpartial c
    |scale*(nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
      t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p)-
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        ((HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re| ≤
      ((Q+1:ℝ)^2*ε+(1/2:ℝ)*(Q+1:ℝ)^4*η)*Coulomb.mass p := by
  let p := finiteTensorState v hv₁ hL2 hpartial c
  let M := fun a b => flatResidualMatrix v r a b+flatNuclearMatrix v F a b
  let T := flatCoulombTensor v
  let x := Laughlin.Fock.normalizedTensorExterior (n+2) Q c
  have he := finiteTensorState_form_compression (n := n) (Q := Q) hdensity v r hv hL2 hpartial hr ho V hV E B t
    hB heq F hN hW c hc hI
  have hscale : HubbardGlobal.oneBodyOperator (fun a b => (scale:ℂ)*M a b)+
      HubbardGlobal.twoBodyOperator (fun a b c d => (scale*t:ℂ)*T a b c d) =
      (scale:ℂ) • (HubbardGlobal.oneBodyOperator M+(t:ℂ) • HubbardGlobal.twoBodyOperator T) := by
    rw [HubbardGlobal.oneBodyOperator_smul,HubbardGlobal.twoBodyOperator_smul,smul_add,smul_smul]
  have hb := occupationInner_operator_error
    (HubbardGlobal.oneBodyOperator (fun a b => (scale:ℂ)*M a b)+
      HubbardGlobal.twoBodyOperator (fun a b c d => (scale*t:ℂ)*T a b c d))
    (HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
    _ (HubbardGlobal.electronicOperator_error _ _ _ _ hK hWerror) x
  rw [hscale,LinearMap.smul_apply,Laughlin.Fock.occupationInner_smul_right] at hb
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hb
  have hm := finiteTensorState_occupationMass v hv₁ hL2 hpartial ho c hc
  change Coulomb.mass p = Laughlin.Fock.occupationNormSq Q x at hm
  rw [← hm] at hb
  change _ = (Laughlin.Fock.occupationInner Q x
    ((HubbardGlobal.oneBodyOperator M+(t:ℂ) • HubbardGlobal.twoBodyOperator T) x)).re at he
  dsimp only
  rw [he]
  exact hb

end FormApproximation

end ContinuumCoulomb

end

end OAI
