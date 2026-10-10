import OAI.Analysis.CircleDomains.Reflection.PrincipalComplexBeltrami
import OAI.Analysis.CircleDomains.Rigidity.PrincipalPhysicalWitness

namespace OAI

/-! The complex principal solution carries an actual local W1,2 witness
and the same coefficient in its physical Wirtinger equation. -/
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalPhysicalWitness_complex_equation (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z))
    (μ : ℂ → ℂ)
    (hq : ∀ᵐ z ∂volume, g z=μ z*(1+beurling g z)) :
    let D := principalPhysicalWitness H g hw
    ∀ᵐ x ∂volume,
      planarDbar (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1) =
      μ (complexPlaneCoordinates x) * (planarDz (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving
  filter_upwards [hmp.ae hq, hmp.ae (principalDirectionalCorrection_ae g 1),
    hmp.ae (principalDirectionalCorrection_ae g Complex.I)] with x hqx h0 h1
  change planarDbar (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).im =
      μ (complexPlaneCoordinates x) * (planarDz (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).im)
  rw [planarDbar_of_complex_directions, planarDz_of_complex_directions]
  simp only [principalWeakDirections, complexPlaneCoordinates_zero,
    complexPlaneCoordinates_one, h0, h1, star_one, Complex.star_def, Complex.conj_I,
    one_mul, neg_mul] at hqx ⊢
  have hb : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))+
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  have hz : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))-
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = 1+beurling g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  simp only [sub_eq_add_neg] at hb hz ⊢
  rw [hb, hz]
  exact hqx

lemma exists_principal_complex_physical (μ : ℂ → ℂ)
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ}
    (hk : 0≤k) (hk1 : k<1) (hb : ∀z,‖μ z‖≤k)
    (hs : ∀z,R≤‖z‖ → μ z=0) :
    ∃(H : ℂ ≃ₜ ℂ) (D : PlaneLocalWeakComplex (fun x => H (complexPlaneCoordinates x))),
      Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᵐ x ∂volume,
        planarDbar (D.realGradient x 0) (D.realGradient x 1)
          (D.imagGradient x 0) (D.imagGradient x 1) =
        μ (complexPlaneCoordinates x) *
          planarDz (D.realGradient x 0) (D.realGradient x 1)
            (D.imagGradient x 0) (D.imagGradient x 1) := by
  obtain ⟨g,H,he,hp,hw⟩ := exists_principal_complex_beltrami_limit μ hm hk hk1 hb hs
  exact ⟨H,principalPhysicalWitness H g hw,hp,
    principalPhysicalWitness_complex_equation H g hw μ he⟩

end CircleDomainRigidity

end

end OAI
