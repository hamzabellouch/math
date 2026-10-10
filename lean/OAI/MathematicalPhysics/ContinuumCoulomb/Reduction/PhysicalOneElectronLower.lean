import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitIntegratedBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ComplexFormSplit
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabRegularity

namespace OAI

/-!
A finite-rank lower bound for the manufactured one-electron Coulomb
field, obtained from the planar and vertical spectral estimates.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def planarSpectralLevel (γ : ℝ) (m : ℕ) (D η : ℝ) : ℝ :=
  -1/2+γ-planarSiteDerivativeBound D^2-
    γ*(1+η⁻¹)*m*planarSiteTailConstant*Real.exp (-(19/20:ℝ)*(D/8))

def verticalSpectralLevel (freq S η : ℝ) : ℝ :=
  3*freq/2-verticalCutoffDerivativeBound S^2/2-
    freq*(1+η⁻¹)*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)

def physicalSeparablePotential {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) (x : Position) : ℝ :=
  splitSeparablePotential u freq S (positionSplitCoordinates x)

theorem physicalSeparablePotential_continuous {m : ℕ} (u : Fin m → PlanarPosition)
    (freq S : ℝ) : Continuous (physicalSeparablePotential u freq S) := by
  unfold physicalSeparablePotential splitSeparablePotential verticalCapPotential
  exact (((planarWellSum_continuous u).comp positionSplitCoordinates.continuous.fst).add
    ((continuous_const.mul ((positionSplitCoordinates.continuous.snd.pow 2).min continuous_const))))

theorem positionRealForm_mono_shift {V W : Position → ℝ} {ε : ℝ}
    (hV : Continuous V) (hW : Continuous W) (hVW : ∀ x, W x-ε ≤ V x)
    {f : Position → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    positionRealForm W f-ε*(∫ x, f x^2) ≤ positionRealForm V f := by
  have hsqc : HasCompactSupport (fun x => f x^2) :=
    hc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hsq : Integrable (fun x => f x^2) :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport hsqc
  have hi (U : Position → ℝ) (hU : Continuous U) : Integrable (fun x => U x*f x^2) := by
    have hcU : HasCompactSupport (fun x => U x*f x^2) := hsqc.mul_left
    exact (hU.mul (hf.continuous.pow 2)).integrable_of_hasCompactSupport hcU
  have h := integral_mono ((hi W hW).sub (hsq.const_mul ε)) (hi V hV)
    (fun x => by
      change W x*f x^2-ε*f x^2 ≤ V x*f x^2
      nlinarith [mul_le_mul_of_nonneg_right (hVW x) (sq_nonneg (f x))])
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi W hW) (hsq.const_mul ε),integral_const_mul] at h
  unfold positionRealForm
  linarith

theorem physicalSeparable_test_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : Position → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η))*(∫ x, f x^2) -
        γ*(1+η)*(∑ i, (∫ x, f x*continuumLocalizedMode freq (u i) x)^2) ≤
        positionRealForm (physicalSeparablePotential u freq S) f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := split_test_spectral_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S hD hη hfreq hS hbarrier u hsep hdom f hf hc => ?_⟩
  have h := hbound m D η freq S hD hη hfreq hS hbarrier u hsep hdom
    (splitPullback f) (splitPullback_contDiff hf) (splitPullback_compact hc)
  rw [← splitSeparableForm_eq u freq S (splitPullback_contDiff hf) (splitPullback_compact hc)] at h
  have hpot : (fun p => physicalSeparablePotential u freq S (positionSplitCoordinates.symm p)) =
      splitSeparablePotential u freq S := by
    funext p
    simp only [physicalSeparablePotential,ContinuousLinearEquiv.apply_symm_apply]
  rw [← hpot,splitPullback_form _ hf] at h
  have hm : (∫ p, splitPullback f p^2) = ∫ x, f x^2 := splitPullback_integral (fun x => f x^2)
  have ho (i : Fin m) : (∫ p, splitPullback f p*localizedMode freq (u i) p) =
      ∫ x, f x*continuumLocalizedMode freq (u i) x := by
    rw [← positionSplitCoordinates_integral (fun p => splitPullback f p*localizedMode freq (u i) p)]
    simp only [splitPullback,ContinuousLinearEquiv.symm_apply_apply,continuumLocalizedMode]
  rw [hm] at h
  simp_rw [ho] at h
  exact h

/-- The actual Coulomb slab and compact counterterm well field have the
same lower bound, up to the proved finite-slab and counterterm errors. -/
theorem manufacturedSlab_test_lower
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ (m : ℕ) (D η freq S rho H scale δ : ℝ),
      8 ≤ D → 0 < η → 0 < freq → 0 < S → 0 ≤ rho → 0 < H → 0 ≤ scale → 0 ≤ δ →
      freq^2 = 4*Real.pi*rho → 3*freq/2 ≤ freq^2*S^2/8 →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      (∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧ localizedCounterterm freq u i/scale ≤ δ) →
      γ*(1+η)*(1+m*localizedOverlapBound D) ≤ freq*(1+η) →
      ∀ f : Position → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      (planarSpectralLevel γ m D η+verticalSpectralLevel freq S η-freq*(1+η)-
        (δ*PlanarSobolev.wellBound+6*Real.pi*rho*S^3/H))*(∫ x, ‖f x‖^2) -
        γ*(1+η)*(∑ i, ‖∫ x, f x*(continuumLocalizedMode freq (u i) x : ℂ)‖^2) ≤
        positionComplexForm (manufacturedSlabPotential rho H S freq scale u) f := by
  obtain ⟨γ,hγ,hsmall,hbound⟩ := physicalSeparable_test_lower hp hv
  refine ⟨γ,hγ,hsmall,fun m D η freq S rho H scale δ hD hη hfreq hS hrho hH hscale hδ
    hrelation hbarrier u hsep hcoeff hdom f hf hc => ?_⟩
  have hseparate (i j : Fin m) (hij : i ≠ j) : 2 ≤ ‖u i-u j‖ := by
    linarith [hsep i j hij]
  apply real_form_lower_to_complex _ (manufacturedSlabPotential_continuous hrho hH.le hS.le _ _ u)
    (fun i => continuumLocalizedMode freq (u i))
    (fun i => continuumLocalizedMode_memLp hfreq (u i)) _ _ ?_ f hf hc
  intro g hg hgc
  have hs := hbound m D η freq S hD hη hfreq hS hbarrier u hsep hdom g hg hgc
  have hvw := positionRealForm_mono_shift
    (manufacturedSlabPotential_continuous hrho hH.le hS.le _ _ u)
    (physicalSeparablePotential_continuous u freq S)
    (manufacturedSlabPotential_lower hrho hH hS.le hscale hrelation u hseparate hδ hcoeff) hg hgc
  nlinarith

end ContinuumCoulomb

end

end OAI
