import OAI.Geometry.IsometricImmersion.Caps.LowerCapInduction

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem fixed_metric_lower_cap_all_derivatives
    {g0 eta : MetricField} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (B : (bStar : ℝ) → ℕ → LowerCapRectangle bStar → ℝ)
      (H : (bStar : ℝ) → ℕ → LowerCapRectangle bStar → ℝ≥0),
      (∀ (bStar : ℝ) (n : ℕ) (r : LowerCapRectangle bStar), 0 ≤ B bStar n r) ∧
      ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
        (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
        (∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|) →
        (∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p) →
        (∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100) →
        (∀ p ∈ modelSquare,
          (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p) →
        ∃ Y : ℝ → ℝ → ℝ,
          ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
          (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
          (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
            HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
              (Icc (-2 : ℝ) 2) t) ∧
          (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
          ∀ (bStar : ℝ) (n : ℕ) (r : LowerCapRectangle bStar),
            CoordinateBound z (r.image Y) n (B bStar n r) ∧
            CoordinateL2Bound z (r.image Y) n (H bStar n r) := by
  classical
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G :=
    fun i j k hk p hp => hgB i j k (by omega) p hp
  have hpoint : ∀ (bStar : ℝ) (n : ℕ) (r : LowerCapRectangle bStar),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        CapInductionHeight (g0+eta) U Z c e0 z →
        CapInductionFlow (g0+eta) U G Z d c e0 kappa z Y W → CoordinateBound z (r.image Y) n B :=
    fun _ n r => uniform_lowerCap_pointwise hg hU hSU hG hZ hd hc hg4 hdet n r
  choose B hB hBest using hpoint
  have hnorm : ∀ (bStar : ℝ) (n : ℕ) (r : LowerCapRectangle bStar),
      ∃ H : ℝ≥0, ∀ (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        CapInductionHeight (g0+eta) U Z c e0 z →
        CapInductionFlow (g0+eta) U G Z d c e0 kappa z Y W → CoordinateL2Bound z (r.image Y) (n+8) H :=
    fun _ n r => uniform_lowerCap_L2 hg hU hSU hG hZ hd hc hg4 hdet n r
  choose H hHest using hnorm
  refine ⟨B,H,hB,?_⟩
  intro z hz hzB hyy hE hsmall hD
  let hh : CapInductionHeight (g0+eta) U Z c e0 z := ⟨hz,hzB,hyy,hE,hsmall,hD⟩
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hg hU hSU hG hZ hd hc he0 hgB hdet hh
    hk hbackground hsupport hcentral
  refine ⟨Y,capChart_contDiffOn hf.jointSmooth,hf.start,hf.ode,hf.displacement,?_⟩
  intro bStar n r
  exact ⟨hBest bStar n r z Y W hh hf,
    (hHest bStar n r z Y W hh hf).mono (by omega) le_rfl⟩

end SmoothLocal.Flow

end

end OAI
