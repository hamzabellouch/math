import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBoundaryOperatorLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalIdentification

namespace OAI

/-! Canonical outgoing columns supply the actual convergent boundary operator
along an arbitrary increasing sequence of matched powers. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem radialMatchedCanonicalBoundary_with_det
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (ell : ℕ) (lam : ℕ → ℂ) (lam₀ : ℂ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re) (R₀ : ℝ) :
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
        (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Y i (lam i)) R)
        (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Z i (lam i)) R)
      let P := spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R
      let N := spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R
      spectralValueDet (spectralPhysicalValueMap P) (spectralPhysicalValueMap N) ≠ 0 ∧
      Tendsto (fun i => spectralFluxBoundary R (radialMatchedMassFunction (s i) (z i) R)
        (radialMatchedTransportFunction (s i) (z i) R)
        (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
          (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop
        (𝓝 (spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
          (radialMatchedFreeTransportFunction z₀ R)
          (spectralGaugeRobin (radialShootingFreeExterior z₀ R)
            (deriv (radialShootingFreeExterior z₀) R) (spectralJetRobin P N)))) ∧
      ∀ᶠ i in atTop, spectralValueDet
        (spectralPhysicalValueMap (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Y i (lam i)) R))
        (spectralPhysicalValueMap (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Z i (lam i)) R)) ≠ 0 := by
  classical
  let N := fun i => s i+radialInnerShootingThreshold
  have hN : StrictMono N := fun i j hij => Nat.add_lt_add_right (hs hij) _
  let ze : ℕ → ProfileMatchingBall := fun n => if h : ∃ i, N i=n then z (Classical.choose h) else z₀
  have hze (i : ℕ) : ze (N i)=z i := by
    dsimp only [ze]
    rw [dite_eq_left (show ∃ j, N j=N i from ⟨i,rfl⟩)]
    congr 1
    exact hN.injective (Classical.choose_spec (show ∃ j, N j=N i from ⟨i,rfl⟩))
  have hzelim : Tendsto ze atTop (𝓝 z₀) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp hz ε hε
    refine ⟨N K,fun n hn => ?_⟩
    by_cases h : ∃ i, N i=n
    · have hi : K ≤ Classical.choose h := hN.le_iff_le.mp (by
        rw [Classical.choose_spec h]
        exact hn)
      simpa only [ze,dite_eq_left h] using hK _ hi
    · simpa only [ze,dite_eq_right h,dist_self] using hε
  let νe := fun n => radialShootingNu n (ze n)
  let me := fun n => radialShootingM (ze n)
  let le := radialParameterExtension N lam lam₀
  have hνe : Tendsto νe atTop (𝓝 (2*Complex.I*(radialShootingB (profileMatchingParameter z₀) : ℂ))) := by
    have ht := radialShootingNu_subsequence_tendsto id strictMono_id ze z₀ hzelim
    have he : -2*radialShootingQ z₀=2*Complex.I*(radialShootingB (profileMatchingParameter z₀) : ℂ) := by
      unfold radialShootingQ
      ring
    simpa only [νe,Function.id_def,he] using ht
  have hme : Tendsto me atTop (𝓝 (radialShootingM z₀)) :=
    continuous_radialShootingM.continuousAt.tendsto.comp hzelim
  have hle : Tendsto le atTop (𝓝 lam₀) := radialParameterExtension_tendsto N hN lam lam₀ hlam
  have hXe : ∀ᶠ n in atTop, HasRadialExterior (νe n) n (me n) (Real.log innerBoundaryRadius) := by
    filter_upwards [radialShootingExterior_exists] with n hn
    exact hn (ze n)
  obtain ⟨δ,ρ,hδ,_hδm,hsmall,_hρ,_hupper,_hlower⟩ := radialShooting_free_annulus z₀
  obtain ⟨R,hRR,_hR1,Y,Z,hYZ,hM,hdet,hactual⟩ := exists_canonical_freePhysical_robin_limit_with_det
    νe me le (radialShootingB (profileMatchingParameter z₀)) (radialShootingM z₀) lam₀ ell
    hνe hme hle (radialShootingM_ne_zero z₀) hlam₀ δ (Real.log innerBoundaryRadius)
    (max R₀ (innerBoundaryRadius+1)) hδ hsmall hXe
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hRR
  have hR : innerBoundaryRadius < R := by have h := (le_max_right _ _).trans hRR; linarith
  refine ⟨R,hR₀,hR,(fun i => Y (N i)),(fun i => Z (N i)),?_,?_⟩
  · simpa only [νe,me,hze,N] using hN.tendsto_atTop.eventually hYZ
  · dsimp only
    refine ⟨hdet,?_,?_⟩
    · apply radialMatchedBoundaryOperator_tendsto s hs z z₀ hz hX hm R hR
      simpa only [Function.comp_def,νe,me,le,radialParameterExtension_apply N hN,hze,N] using hM.comp hN.tendsto_atTop
    · simpa only [νe,le,radialParameterExtension_apply N hN,hze,N] using
        hN.tendsto_atTop.eventually hactual

theorem radialMatchedCanonicalBoundary
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (ell : ℕ) (lam : ℕ → ℂ) (lam₀ : ℂ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (hlam₀ : -(1/32 : ℝ) ≤ lam₀.re) (R₀ : ℝ) :
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
        (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Y i (lam i)) R)
        (spectralPhysicalPair (ν i-2*lam i) (star (ν i)-2*lam i) (Z i (lam i)) R)
      let P := spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R
      let N := spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z₀)) lam₀ R
      spectralValueDet (spectralPhysicalValueMap P) (spectralPhysicalValueMap N) ≠ 0 ∧
      Tendsto (fun i => spectralFluxBoundary R (radialMatchedMassFunction (s i) (z i) R)
        (radialMatchedTransportFunction (s i) (z i) R)
        (spectralGaugeRobin (radialMatchedProfile (s i) (z i) R)
          (deriv (radialMatchedProfile (s i) (z i)) R) (M i))) atTop
        (𝓝 (spectralFluxBoundary R (radialMatchedFreeMassFunction z₀ R)
          (radialMatchedFreeTransportFunction z₀ R)
          (spectralGaugeRobin (radialShootingFreeExterior z₀ R)
            (deriv (radialShootingFreeExterior z₀) R) (spectralJetRobin P N)))) := by
  obtain ⟨R,hR₀,hR,Y,Z,hYZ,hdet,hlim,_⟩ := radialMatchedCanonicalBoundary_with_det
    s hs z z₀ hz hX hm ell lam lam₀ hlam hlam₀ R₀
  exact ⟨R,hR₀,hR,Y,Z,hYZ,hdet,hlim⟩

end DefocusingNLS

end OAI
