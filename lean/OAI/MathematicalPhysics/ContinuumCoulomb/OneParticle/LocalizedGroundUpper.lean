import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardForm
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardVariationalWitness
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.TensorTrial
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PhysicalGroundComparison

namespace OAI

/-! The finite Hubbard variational bottom supplies admissible trials for
the full continuum problem, including the exact physical energy offset. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal Laughlin.Fock

section LocalizedUpper
variable (hdensity : PublishedSobolevSmoothDensity)
variable {Edge : Type*} [Fintype Edge]
variable {n m : ℕ} {rho H S freq scale δ D εK : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hf : 0 < freq)
variable (hrelation : freq^2=4*Real.pi*rho) (hscale : 0 < scale)
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
  hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ εK)
variable (hI : ∀ w : Coulomb.H1Vector (n+2), nuclearFormIntegrable F w)
variable (hNelec : n+2=m+1)

include hdensity hrho hH hS hf hrelation hscale hsep hs hδ hcoeff hN hK hI hNelec

theorem localized_hubbard_near_trial (ε : ℝ) (hε : 0 < ε) :
    ∃ w : Coulomb.H1Vector (n+2), Coulomb.Antisymmetric w ∧ 0 < Coulomb.mass w ∧
      nuclearPerturbedForm (fun x => ∑ i, manufacturedSlabPotential rho H S freq scale u
        (Coulomb.position x i)) F w+scale⁻¹*Coulomb.pairEnergy w ≤
      ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+
        (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
          localizedHubbardFormError m freq D εK)/scale+ε)*Coulomb.mass w := by
  have ht : ∃ c : Laughlin.State (n+2) (2*m+1), Laughlin.Antisymmetric c ∧
      0 < fockMass (normalizedTensorExterior (n+2) (2*m+1) c) ∧
      hubbardFermionForm m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t (normalizedTensorExterior (n+2) (2*m+1) c) <
      (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t+scale*ε)*fockMass (normalizedTensorExterior (n+2) (2*m+1) c) := by
    rw [hNelec]
    exact hubbardFermionBottom_tensor_approximate m
      (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u) left right t
      (mul_pos hscale hε)
  obtain ⟨c,hc,hm,ht⟩ := ht
  let w := finiteTensorState (localizedSpinMode freq u) (localizedSpinMode_C1 freq u)
    (localizedSpinMode_memLp hf u) (localizedSpinMode_partial_memLp hf u) c
  have hm' := finiteTensorState_mass_eq_fockMass (localizedSpinMode freq u)
    (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
    (localizedSpinMode_partial_memLp hf u) (localizedSpinMode_inner hf u hsep hs) c hc
  refine ⟨w,finiteTensorState_antisymmetric _ _ _ _ c hc,?_,?_⟩
  · change Coulomb.mass w = _ at hm'
    rwa [hm']
  · have hu := localizedTensor_hubbard_upper hdensity hrho hH hS hf hrelation hscale u hsep hs
      hδ hcoeff F hN left right t hK c hc (hI w) hNelec
      (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t+scale*ε) ht.le
    apply (mul_le_mul_iff_right₀ hscale).mp
    dsimp only at hu
    dsimp only [w]
    convert hu using 1
    field_simp [ne_of_gt hscale]
    ring

theorem localized_hubbard_physical_upper {M : ℕ} (nuc : Coulomb.Nuclei M)
    (offset : ℝ)
    (hsplit : ∀ y, manufacturedSlabPotential rho H S freq scale u y+F y =
      -scale⁻¹*Coulomb.attraction nuc y-offset) :
    formGroundEnergy (dilatedNuclei nuc scale hscale.ne') (n+2) ≤
      ((scale^2*(n+2:ℝ)*(((-1/2:ℝ)+freq/2)+offset)+
        scale*(hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
          localizedHubbardFormError m freq D εK):ℝ):EReal) := by
  have hu := formGroundEnergy_dilated_upper nuc (manufacturedSlabPotential rho H S freq scale u)
    F hscale offset hsplit hI
    ((n+2:ℝ)*((-1/2:ℝ)+freq/2)+
      (hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
        left right t-(1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)+
        localizedHubbardFormError m freq D εK)/scale)
    (localized_hubbard_near_trial hdensity hrho hH hS hf hrelation hscale u hsep hs
      hδ hcoeff F hN left right t hK hI hNelec)
  convert hu using 2
  simp only [Nat.cast_add,Nat.cast_ofNat]
  field_simp [ne_of_gt hscale]
  ring

end LocalizedUpper
end ContinuumCoulomb

end

end OAI
