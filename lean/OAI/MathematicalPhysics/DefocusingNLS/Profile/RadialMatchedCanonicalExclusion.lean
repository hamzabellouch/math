import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCanonicalBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HarmonicRadialNonvanishing

namespace OAI

/-! Canonical columns and the actual penalty family instantiate every
coefficient and boundary limit in physical eigenmode exclusion. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonical_exclusion
    (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hζ₀ : -(1/32 : ℝ)≤ζ₀.re)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) ζ₀ ≠ 0) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ ≤ R ∧ innerBoundaryRadius < R ∧ ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ i in atTop,
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i) ∧
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i)) ∧
      let ν := fun i => radialShootingNu (s i+radialInnerShootingThreshold) (z i)
      let M := fun i => spectralJetRobin
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R)
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)
      ∀ᶠ i in atTop, ∀ f g : ℝ → ℂ, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
        IsHarmonicRadialEigenpair (radialShootingA (s i))
          (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
          (radialMatchedProfile (s i) (z i)) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) (ζ i) f g →
        (deriv f R,deriv g R)=M i (f R,g R) →
        ∀ r ∈ Ioc 0 R, f r=0 ∧ g r=0 := by
  obtain ⟨R,hRR,hR,Y,Z,hYZ,hdet,hB⟩ := radialMatchedCanonicalBoundary s hs z z₀ hz hX hm
    ell ζ ζ₀ hζ hζ₀ (max R₀ (radialShootingR (profileMatchingParameter z₀)+1))
  have hLR : radialShootingR (profileMatchingParameter z₀)<R := by
    have h := (le_max_right R₀ (radialShootingR (profileMatchingParameter z₀)+1)).trans hRR
    linarith
  let ν := fun i => radialShootingNu (s i+radialInnerShootingThreshold) (z i)
  let M := fun i => spectralJetRobin
    (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R)
    (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)
  let B₀ := spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
    (radialMatchedFreeTransportFunction z₀ R)
    (spectralGaugeRobin (radialShootingFreeExterior z₀ R) (deriv (radialShootingFreeExterior z₀) R)
      (spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)))
  change Tendsto (fun i => spectralFluxBoundary R (radialMatchedMassFunction (s i) (z i) R)
    (radialMatchedTransportFunction (s i) (z i) R)
    (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
      (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop (𝓝 B₀) at hB
  obtain ⟨N,F,hw,hmass,hp,ha,_⟩ := radialMatched_penaltyFamily s hs z z₀ hz hX hm R hR.le
  let t := fun i => s (i+N)
  let y := fun i => z (i+N)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij N)
  have hshift : Tendsto (fun i : ℕ => i+N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i+radialInnerShootingThreshold) (y i))
      (t i+radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) := hX (i+N)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i)=0 := hm (i+N)
  have he := radialMatchedPhysical_eventually_zero ell t ht y z₀ hy hXt hmt hz₁ hz₀
    R hLR F hmass hw hp ha (fun i => ζ (i+N)) ζ₀ (hζ.comp hshift) hζ₀
    (fun i => M (i+N)) B₀ (hB.comp hshift) rfl hdet hD
  refine ⟨R,(le_max_left _ _).trans hRR,hR,Y,Z,hYZ,?_⟩
  dsimp only
  rw [← map_add_atTop_eq_nat N]
  exact he

theorem radialMatchedCanonical_global_exclusion
    (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hζ₀ : -(1/32 : ℝ)≤ζ₀.re)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) ζ₀ ≠ 0) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ ≤ R ∧ innerBoundaryRadius < R ∧ ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ i in atTop,
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i) ∧
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i)) ∧
      let ν := fun i => radialShootingNu (s i+radialInnerShootingThreshold) (z i)
      let M := fun i => spectralJetRobin
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R)
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)
      ∀ᶠ i in atTop, ∀ f g : ℝ → ℂ, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
        IsHarmonicRadialEigenpair (radialShootingA (s i))
          (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
          (radialMatchedProfile (s i) (z i)) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) (ζ i) f g →
        (deriv f R,deriv g R)=M i (f R,g R) →
        ∀ r : ℝ, 0 < r → f r=0 ∧ g r=0 := by
  obtain ⟨R,hRR,hR,Y,Z,hYZ,hno⟩ := radialMatchedCanonical_exclusion ell s hs z z₀ hz hX hm
    hz₁ hz₀ ζ ζ₀ hζ hζ₀ hD R₀
  refine ⟨R,hRR,hR,Y,Z,hYZ,?_⟩
  dsimp only at hno ⊢
  filter_upwards [hno] with i hi
  intro f g hf hg he hb
  exact harmonicRadialEigenpair_zero_of_ball _ _ _ _ f g _ _
    (radialMatchedProfile_differentiable (s i) (z i) (hX i) (hm i)).continuous.continuousOn
    hf hg he R (((by norm_num : (0 : ℝ)<1).trans_le innerBoundaryRadius_bounds.1).trans hR)
    (hi f g hf hg he hb)

theorem radialMatchedCanonical_exclusion_with_det
    (ell : ℕ) (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (hz₁ : z₀.val.1=0) (hz₀ : diskProfile (profileMatchingParameter z₀)=0)
    (ζ : ℕ → ℂ) (ζ₀ : ℂ) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (hζ₀ : -(1/32 : ℝ)≤ζ₀.re)
    (hD : spectralSlowDeterminant ell (radialShootingB (profileMatchingParameter z₀))
      ((radialShootingR (profileMatchingParameter z₀))^2/4) ζ₀ ≠ 0) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ ≤ R ∧ innerBoundaryRadius < R ∧ ∃ Y Z : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ i in atTop,
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (1,0) (Y i) ∧
        IsCanonicalHolomorphicColumn (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
          ((ell*(ell+10) : ℕ) : ℂ) (radialShootingM (z i))
          (s i+radialInnerShootingThreshold) (Real.log innerBoundaryRadius) (0,1) (Z i)) ∧
      let ν := fun i => radialShootingNu (s i+radialInnerShootingThreshold) (z i)
      let M := fun i => spectralJetRobin
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R)
        (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)
      ∀ᶠ i in atTop, spectralValueDet
        (spectralPhysicalValueMap (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R))
        (spectralPhysicalValueMap (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)) ≠ 0 ∧
        ∀ f g : ℝ → ℂ, ContDiff ℝ 2 f → ContDiff ℝ 2 g →
        IsHarmonicRadialEigenpair (radialShootingA (s i))
          (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
          (radialMatchedProfile (s i) (z i)) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) (ζ i) f g →
        (deriv f R,deriv g R)=M i (f R,g R) →
        ∀ r ∈ Ioc 0 R, f r=0 ∧ g r=0 := by
  obtain ⟨R,hRR,hR,Y,Z,hYZ,hdet,hB,hactual⟩ := radialMatchedCanonicalBoundary_with_det s hs z z₀ hz hX hm
    ell ζ ζ₀ hζ hζ₀ (max R₀ (radialShootingR (profileMatchingParameter z₀)+1))
  have hLR : radialShootingR (profileMatchingParameter z₀)<R := by
    have h := (le_max_right R₀ (radialShootingR (profileMatchingParameter z₀)+1)).trans hRR
    linarith
  let ν := fun i => radialShootingNu (s i+radialInnerShootingThreshold) (z i)
  let M := fun i => spectralJetRobin
    (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Y i (ζ i)) R)
    (spectralPhysicalPair (ν i-2*ζ i) (star (ν i)-2*ζ i) (Z i (ζ i)) R)
  let B₀ := spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
    (radialMatchedFreeTransportFunction z₀ R)
    (spectralGaugeRobin (radialShootingFreeExterior z₀ R) (deriv (radialShootingFreeExterior z₀) R)
      (spectralJetRobin
        (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)
        (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) ζ₀ R)))
  change Tendsto (fun i => spectralFluxBoundary R (radialMatchedMassFunction (s i) (z i) R)
    (radialMatchedTransportFunction (s i) (z i) R)
    (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
      (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop (𝓝 B₀) at hB
  obtain ⟨N,F,hw,hmass,hp,ha,_⟩ := radialMatched_penaltyFamily s hs z z₀ hz hX hm R hR.le
  let t := fun i => s (i+N)
  let y := fun i => z (i+N)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij N)
  have hshift : Tendsto (fun i : ℕ => i+N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i+radialInnerShootingThreshold) (y i))
      (t i+radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) := hX (i+N)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i)=0 := hm (i+N)
  have he := radialMatchedPhysical_eventually_zero ell t ht y z₀ hy hXt hmt hz₁ hz₀
    R hLR F hmass hw hp ha (fun i => ζ (i+N)) ζ₀ (hζ.comp hshift) hζ₀
    (fun i => M (i+N)) B₀ (hB.comp hshift) rfl hdet hD
  refine ⟨R,(le_max_left _ _).trans hRR,hR,Y,Z,hYZ,?_⟩
  dsimp only
  rw [← map_add_atTop_eq_nat N]
  exact (hshift.eventually hactual).and he

end DefocusingNLS

end OAI
