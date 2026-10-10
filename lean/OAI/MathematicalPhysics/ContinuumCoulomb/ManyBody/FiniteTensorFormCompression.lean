import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorKineticCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.PairTensorCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearPerturbedComplement

namespace OAI

/-! Exact compression of the interacting continuum form, including the
singular nuclear term, to the actual finite CAR Hamiltonian. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

namespace HubbardGlobal

theorem oneBodyOperator_add {Q : ℕ} (K L : Fin (Q+1) → Fin (Q+1) → ℂ) :
    oneBodyOperator (fun a b => K a b+L a b) = oneBodyOperator K+oneBodyOperator L := by
  simp only [oneBodyOperator,add_smul,Finset.sum_add_distrib]

end HubbardGlobal

def flatResidualMatrix {Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (a b : Fin (Q+1)) : ℂ :=
  ∫ z, star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (r b) z
    ∂Coulomb.spinSpaceMeasure

def flatNuclearMatrix {Q : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (F : Position → ℝ) (a b : Fin (Q+1)) : ℂ :=
  ∫ z, (F (WithLp.toLp 2 z.2):ℂ)*
    (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z)
    ∂Coulomb.spinSpaceMeasure

def flatCoulombTensor {Q : ℕ} (v : Fin (Q+1) → Position → Fin 2 → ℂ)
    (a b c d : Fin (Q+1)) : ℂ :=
  ∫ z, flatPairCoulomb z.1 z.2*
    ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
      (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2))
    ∂(Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure)

theorem finiteTensorState_form_compression (hdensity : PublishedSobolevSmoothDensity)
    {n Q : ℕ} (v r : Fin (Q+1) → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (hr : ∀ a s, MemLp (fun x => r a x s) 2)
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)
    (V : Position → ℝ) (hV : Continuous V) (E B t : ℝ)
    (hB : ∀ x : Configuration (n+2), |∑ i, V (Coulomb.position x i)| ≤ B)
    (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)
    (F : Position → ℝ)
    (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
      Coulomb.spinSpaceMeasure)
    (hW : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))
    (c : Laughlin.State (n+2) Q) (hc : Laughlin.Antisymmetric c)
    (hI : ∀ s i, Integrable (fun x => F (Coulomb.position x i)*
      ‖(finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c).value s x‖^2)) :
    let p := finiteTensorState v (fun a s => (hv a s).of_le (by norm_num)) hL2 hpartial c
    nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
      t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        ((HubbardGlobal.oneBodyOperator (fun a b => flatResidualMatrix v r a b+flatNuclearMatrix v F a b)+
          (t:ℂ) • HubbardGlobal.twoBodyOperator (flatCoulombTensor v))
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re := by
  let hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s) :=
    fun a s => (hv a s).of_le (by norm_num)
  let p := finiteTensorState v hv₁ hL2 hpartial c
  have hb := finiteTensorState_bounded_compression (n := n+1) hdensity v r hv hL2 hpartial
    hr ho V hV E B hB heq c hc
  have hn := congrArg Complex.re
    (finiteTensorState_nuclear_compression v hv₁ hL2 hpartial ho c hc F hN hI)
  have hp := congrArg Complex.re (finiteTensorState_pair_compression v hv₁ hL2 hpartial ho hW c hc)
  simp only [Complex.ofReal_re] at hn hp
  change nuclearPerturbedForm _ F p+t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p = _
  simp only [HubbardGlobal.oneBodyOperator_add,LinearMap.add_apply,LinearMap.smul_apply,
    Laughlin.Fock.occupationInner_add_right,Laughlin.Fock.occupationInner_smul_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change _ = (Laughlin.Fock.occupationInner Q _
      (HubbardGlobal.oneBodyOperator (flatResidualMatrix v r) _)).re+
    (Laughlin.Fock.occupationInner Q _ (HubbardGlobal.oneBodyOperator (flatNuclearMatrix v F) _)).re+
    t*(Laughlin.Fock.occupationInner Q _ (HubbardGlobal.twoBodyOperator (flatCoulombTensor v) _)).re
  change nuclearErrorEnergy F p =
    (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
      (HubbardGlobal.oneBodyOperator (flatNuclearMatrix v F)
        (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re at hn
  change Coulomb.pairEnergy p =
    (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
      (HubbardGlobal.twoBodyOperator (flatCoulombTensor v)
        (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re at hp
  rw [← hn,← hp]
  have hb' : boundedPotentialForm (fun x => ∑ i, V (Coulomb.position x i)) p-
      (n+2:ℝ)*E*Coulomb.mass p =
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        (HubbardGlobal.oneBodyOperator (flatResidualMatrix v r)
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re := by
    convert hb using 1 <;> first | rfl | (push_cast; ring)
  rw [← hb']
  unfold nuclearPerturbedForm
  ring

end ContinuumCoulomb

end

end OAI
