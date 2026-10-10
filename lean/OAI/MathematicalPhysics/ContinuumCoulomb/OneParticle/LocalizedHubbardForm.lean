import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardEntries
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorFormError
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorOccupationSector
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedTensorDiagonal

namespace OAI

/-! The actual manufactured continuum form on its localized tensor space
is controlled by the full half-filled Hubbard variational problem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal Laughlin.Fock

theorem nuclearFormIntegrable_of_absolute {n : ℕ} (F : Position → ℝ)
    (hF : Measurable F) (p : Coulomb.H1Vector n)
    (hI : ∀ s i, Integrable (fun x => |F (Coulomb.position x i)| * ‖p.value s x‖^2)) :
    nuclearFormIntegrable F p := by
  intro s i
  have h := (weighted_inner_pairing volume (fun x => F (Coulomb.position x i))
    (p.value s) (p.value s)
    (hF.comp (Coulomb.positionCLM i).continuous.measurable).aemeasurable
    (p.value_L2 s).aestronglyMeasurable (p.value_L2 s).aestronglyMeasurable
    (hI s i) (hI s i)).1
  simpa only [real_inner_self_eq_norm_sq] using h

def localizedHubbardFormError (m : ℕ) (freq D ε : ℝ) : ℝ :=
  (2*m+1+1:ℝ)^2*ε+(1/2:ℝ)*(2*m+1+1:ℝ)^4*
    ((m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
      localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D))

section LocalizedForm
variable (hdensity : PublishedSobolevSmoothDensity)
variable {Edge : Type*} [Fintype Edge]
variable {n m : ℕ} {rho H S freq scale δ D ε : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hf : 0 < freq)
variable (hrelation : freq^2 = 4*Real.pi*rho) (hscale : 0 < scale)
variable (u : Fin (m+1) → PlanarPosition)
variable (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
variable (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
variable (hδ : 0 ≤ δ)
variable (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
  localizedCounterterm freq u i/scale ≤ δ)
variable (F : Position → ℝ)
variable (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
  (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z)*
    Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z)) Coulomb.spinSpaceMeasure)
variable (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
variable (hK : ∀ a b, ‖(scale:ℂ)*
  (flatResidualMatrix (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u) a b+
    flatNuclearMatrix (localizedSpinMode freq u) F a b)-
  hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ ε)
variable (c : Laughlin.State (n+2) (2*m+1)) (hc : Laughlin.Antisymmetric c)
variable (hI : nuclearFormIntegrable F (finiteTensorState (localizedSpinMode freq u)
  (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
  (localizedSpinMode_partial_memLp hf u) c))

include hdensity hrho hH hS hf hrelation hscale hsep hs hδ hcoeff hN hK hc hI

theorem localizedTensor_hubbard_form_error :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
    let x := normalizedTensorExterior (n+2) (2*m+1) c
    |scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p-
        (n+2:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)-
      (occupationInner (2*m+1) x
        ((oneBodyOperator (hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t)+
          twoBodyOperator (hubbardCoulombTensor m (localizedCoulombProfile freq 0)
            (localizedOffsiteCoulomb freq u))) x)).re| ≤
      localizedHubbardFormError m freq D ε*Coulomb.mass p := by
  obtain ⟨B,hB⟩ := manufacturedSlabPotential_bounded hrho hH.le hS freq scale u
  have hsum (z : Configuration (n+2)) :
      |∑ i, manufacturedSlabPotential rho H S freq scale u (Coulomb.position z i)| ≤
        (n+2:ℝ)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_ofNat] using Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => hB (Coulomb.position z i))
  have he := finiteTensorState_form_approximation (n := n) (Q := 2*m+1) hdensity
    (localizedSpinMode freq u) (localizedSpinResidual rho H S freq scale u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_C2 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u)
    (localizedSpinResidual_memLp hrho hH.le hS.le hf scale u hδ hcoeff)
    (localizedSpinMode_inner hf u hsep hs)
    (manufacturedSlabPotential rho H S freq scale u)
    (manufacturedSlabPotential_continuous hrho hH.le hS.le freq scale u)
    ((-1/2:ℝ)+freq/2) ((n+2:ℝ)*B) scale⁻¹ hsum
    (fun a s x => by
      simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
        Complex.ofReal_one,Complex.ofReal_ofNat] using
        localizedSpinResidual_operator hrelation H S scale u a s x)
    F hN (localizedSpinMode_coulomb_integrable hf u) c hc hI scale ε
    ((m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
      localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D))
    (hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t)
    (hubbardCoulombTensor m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)) hK
    (fun a b c d => by
      rw [← Complex.ofReal_mul,mul_inv_cancel₀ (ne_of_gt hscale),Complex.ofReal_one,one_mul]
      exact localizedSpinMode_hubbard_tensor_error hf u hsep hs a b c d)
  simpa only [localizedHubbardFormError,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using he

theorem localizedTensor_hubbard_lower (hNelec : n+2=m+1) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
    (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+
      hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-
      localizedHubbardFormError m freq D ε)*Coulomb.mass p ≤
      scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p) := by
  let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
  let x := normalizedTensorExterior (n+2) (2*m+1) c
  have hx : IsHalfFilled m x := by
    intro A hA
    exact normalizedTensorExterior_occupationSupport c A (by omega)
  have hm := finiteTensorState_occupationMass (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs) c hc
  rw [occupationNormSq_fockCoordinates,fockCoordinates_norm_sq] at hm
  have he := localizedTensor_hubbard_form_error hdensity hrho hH hS hf hrelation hscale u hsep hs
    hδ hcoeff F hN left right t hK c hc hI
  have hl := hubbardCAR_approximation_lower m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) (localizedOffsiteCoulomb_symmetric hf u)
    (localizedOffsiteCoulomb_diagonal freq u) left right t x hx
    (scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
      (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p-
      (n+2:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)) (localizedHubbardFormError m freq D ε) (by
        change Coulomb.mass p = fockMass x at hm
        rw [← hm]
        exact he)
  change Coulomb.mass p = fockMass x at hm
  rw [← hm] at hl
  dsimp only
  nlinarith only [hl]

theorem localizedTensor_hubbard_upper (hNelec : n+2=m+1) (a : ℝ)
    (htrial : hubbardFermionForm m (localizedCoulombProfile freq 0)
      (localizedOffsiteCoulomb freq u) left right t
      (normalizedTensorExterior (n+2) (2*m+1) c) ≤
      a*fockMass (normalizedTensorExterior (n+2) (2*m+1) c)) :
    let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
      (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
    scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p) ≤
      (scale*(n+2:ℝ)*((-1/2:ℝ)+freq/2)+a-
        (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
        localizedHubbardFormError m freq D ε)*Coulomb.mass p := by
  let p := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
  let x := normalizedTensorExterior (n+2) (2*m+1) c
  have hx : IsHalfFilled m x := by
    intro A hA
    exact normalizedTensorExterior_occupationSupport c A (by omega)
  have hm := finiteTensorState_occupationMass (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs) c hc
  rw [occupationNormSq_fockCoordinates,fockCoordinates_norm_sq] at hm
  have he := localizedTensor_hubbard_form_error hdensity hrho hH hS hf hrelation hscale u hsep hs
    hδ hcoeff F hN left right t hK c hc hI
  have hu := hubbardCAR_approximation_upper m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) (localizedOffsiteCoulomb_symmetric hf u)
    (localizedOffsiteCoulomb_diagonal freq u) left right t x hx
    (scale*(nuclearPerturbedForm (fun z => ∑ i, manufacturedSlabPotential rho H S freq scale u
      (Coulomb.position z i)) F p+scale⁻¹*Coulomb.pairEnergy p-
      (n+2:ℝ)*((-1/2:ℝ)+freq/2)*Coulomb.mass p)) (localizedHubbardFormError m freq D ε) a (by
        change Coulomb.mass p = fockMass x at hm
        rw [← hm]
        exact he) htrial
  change Coulomb.mass p = fockMass x at hm
  rw [← hm] at hu
  dsimp only
  nlinarith only [hu]

end LocalizedForm

end ContinuumCoulomb

end

end OAI
