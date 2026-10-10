import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGeneralizedExclusion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeValueRadius
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalSelection

namespace OAI

/-! No sequence of actual finite-energy radial Jordan pairs approaches a symmetry value. -/

open Filter Topology Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedMode_no_generalized_limit (hRou : RectangleRouche) (ell N : ℕ) (hN : 7 ≤ N)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (x : ℕ → ℂ) (lam₀ : ℂ) (hx : Tendsto x atTop (𝓝 lam₀))
    (hsym : (ell=0 ∧ (lam₀=0 ∨ lam₀=1)) ∨ (ell=1 ∧ lam₀=1/2))
    (hnonneg : ∀ i, 0≤(x i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i))
    (v w : ℕ → ℝ → ℂ) (hv : ∀ i, ContDiff ℝ 2 (v i)) (hw₂ : ∀ i, ContDiff ℝ 2 (w i))
    (he : ∀ i, IsHarmonicRadialSourcePair (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i)
      (v i) (w i) (mode i).first (mode i).second)
    (hvt : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (v i) r‖^2) (Ioi 0))
    (hwt : ∀ i, IntegrableOn (fun r => r^11*‖iteratedDeriv N (w i) r‖^2) (Ioi 0))
    (hb : ∀ i, ∃ M : ℝ, 0≤M ∧ ∀ r, ‖(v i r,w i r)‖≤M) : False := by
  obtain ⟨hz₁,hz₀⟩ := radialMatchingMap_zero_limit s hs.tendsto_atTop z z₀ hz hm
  have hhalf₀ : -(1/32 : ℝ) ≤ lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨R,hR,hLR,hdet⟩ := radialFreeValueDet_large_radius ell z₀ lam₀ hhalf₀
  obtain ⟨K,F,hw,hmass,hp,ha,_⟩ := radialMatched_penaltyFamily s hs z z₀ hz hX hm R hR.le
  let t := fun i => s (i+K)
  let y := fun i => z (i+K)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij K)
  have hshift : Tendsto (fun i : ℕ => i+K) atTop atTop := tendsto_add_atTop_nat K
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i+radialInnerShootingThreshold) (y i))
      (t i+radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) := hX (i+K)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i)=0 := hm (i+K)
  obtain ⟨Y,hY⟩ := radialMatched_exists_canonical_column t y hXt ell (1,0)
  obtain ⟨Z,hZ⟩ := radialMatched_exists_canonical_column t y hXt ell (0,1)
  have hh := radialMatchedCanonical_no_generalized_mode hRou t ht y z₀ hy hz₁ hz₀ hXt hmt ell N hN
    Y Z hY hZ R hR hLR F hmass hw hp ha lam₀ hsym hdet
    (fun i => x (i+K)) (hx.comp hshift) (fun i => hnonneg (i+K))
  obtain ⟨i,hi⟩ := hh.exists
  exact hi (mode (i+K)) (v (i+K)) (w (i+K)) (hv (i+K)) (hw₂ (i+K)) (he (i+K))
    (hvt (i+K)) (hwt (i+K)) (hb (i+K))

end DefocusingNLS

end OAI
