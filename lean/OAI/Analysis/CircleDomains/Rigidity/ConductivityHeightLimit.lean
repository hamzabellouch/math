import OAI.Analysis.CircleDomains.Rigidity.ConductivityHeightCompactness
import OAI.Analysis.CircleDomains.Sobolev.WeakHeightNull

namespace OAI

/-! The continuous height limit and its actual weak derivatives, with the
original error budget and zero gradient on the conductivity support. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_conductivity_height_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (φ : ℕ → ℂ ≃ₜ ℂ)
    (D : ∀ n, PlaneLocalWeakComplex (fun p => φ n (complexPlaneCoordinates p)))
    {B R : ℝ} (hB0 : 0 ≤ B) (hR : 0 < R)
    (hI : ∀ n, Integrable (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2))
    (hB : ∀ n, (∫ p, (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) ≤ B)
    (hh : ∀ n, DifferentiableOn ℂ (φ n) {z | R < ‖z‖})
    (hnorm : ∀ n, (fun z => φ n z-z) =O[cobounded ℂ] (fun z => z⁻¹))
    {F : Set EuclideanPlane} (hF : IsCompact F)
    (hFE : Tendsto (fun n => ∫ p in F,
      (D n).imagGradient p 0^2+(D n).imagGradient p 1^2) atTop (𝓝 0)) :
    ∃ (v : C(ℂ, ℝ)) (G₀ G₁ : Lp ℝ 2 (volume : Measure EuclideanPlane)) (s : ℕ → ℕ),
      StrictMono s ∧ TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop ∧
      DeGiorgi.HasWeakGrad (heightLimitGradient G₀ G₁) (v ∘ complexPlaneCoordinates) univ ∧
      (∫ p, G₀ p^2+G₁ p^2) ≤ B ∧
      (∀ᵐ p ∂volume.restrict F, heightLimitGradient G₀ G₁ p = 0) := by
  obtain ⟨v, s₀, hs₀, hv⟩ := conductivity_height_subsequence harea φ D hB0 hR hI hB hh hnorm
  obtain ⟨G₀, G₁, s₁, hs₁, h₀, h₁, henergy⟩ := conductivity_weak_error_fields
    (fun n p => φ (s₀ n) (complexPlaneCoordinates p)) (fun n => D (s₀ n))
    (fun n => hI (s₀ n)) (fun n => hB (s₀ n))
  let s := s₀ ∘ s₁
  have hs : StrictMono s := hs₀.comp hs₁
  have hlim : TendstoLocallyUniformly (fun n z => (φ (s n) z).im) v atTop := by
    intro U hU z
    obtain ⟨O, hO, h⟩ := hv U hU z
    exact ⟨O, hO, hs₁.tendsto_atTop.eventually h⟩
  have hpoint (p : EuclideanPlane) :
      Tendsto (fun n => (φ (s n) (complexPlaneCoordinates p)).im) atTop
        (𝓝 (v (complexPlaneCoordinates p))) :=
    hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)
  have hbounded (K : Set EuclideanPlane) (hK : IsCompact K) :
      ∃ C : ℝ, ∀ n p, p ∈ K → ‖(φ (s n) (complexPlaneCoordinates p)).im‖ ≤ C := by
    obtain ⟨S, hS⟩ := hK.isBounded.subset_ball 0
    let T := max (2*R) S
    refine ⟨T+R, ?_⟩
    intro n p hp
    have hpT : complexPlaneCoordinates p ∈ closedBall 0 T := by
      have hpS : ‖p‖ < S := by simpa only [mem_ball, dist_zero_right] using hS hp
      simpa only [mem_closedBall, dist_zero_right, complexPlaneCoordinates_norm] using
        hpS.le.trans (le_max_right (2*R) S)
    simpa only [Real.norm_eq_abs] using normalized_homeomorphic_height_bound harea hR
      (le_max_left (2*R) S) (hh (s n)) (hnorm (s n)) (complexPlaneCoordinates p) hpT
  have hw := weak_height_identification (fun n p => φ (s n) (complexPlaneCoordinates p))
    (fun n => D (s n)) (fun n => (φ (s n)).continuous.comp complexPlaneCoordinates.continuous)
    hpoint hbounded (fun n => hI (s n)) G₀ G₁ h₀ h₁
  have hz := weak_height_gradient_zero (fun n p => φ (s n) (complexPlaneCoordinates p))
    (fun n => D (s n)) (fun n => hI (s n)) G₀ G₁ h₀ h₁ hF.measurableSet
    hF.measure_lt_top (hFE.comp hs.tendsto_atTop)
  exact ⟨v, G₀, G₁, s, hs, hlim, hw, henergy, hz⟩

end CircleDomainRigidity

end

end OAI
