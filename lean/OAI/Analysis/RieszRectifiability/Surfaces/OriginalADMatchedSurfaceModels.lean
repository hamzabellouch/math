import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.OriginalADUniformPrecisionAreaModels
import OAI.Analysis.RieszRectifiability.Surfaces.ActualNativeSurfaceGeometry
import OAI.Analysis.RieszRectifiability.Surfaces.MatchedSurfacePrecision

namespace OAI

/-!
# Matched surface models for an AD-regular measure

Uniform-precision area models combine with the native surface geometry to give
matched projection coverage at every scale. The top-mass and AD constants are
chosen before the precision and support cell, while the resulting surface keeps
its exact support, infinite support diameter, and two-sided growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem exists_original_AD_matched_surface_models {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular n μ) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 72057594037927936 → activeProjectionError d ε ≤ 1 / 4096 →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            let ν := nativeSurfaceArea n (Set.range f)
            ν.Regular ∧ ν.support = Set.range f ∧ ADRegular n ν ∧ ediam ν.support = ⊤ ∧
              GlobalUpperGrowth n K ν ∧
              (∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
                ENNReal.ofReal (r ^ n / K) ≤ ν (ball p r)) ∧
              ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
                ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
                  (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
                    infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
                      (281474976710656 * (ε + activeProjectionError d ε)) * r) ∧
                  closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
                    P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)) := by
  obtain ⟨Ktop, hKtop, C, hC, c, hc, hcfin, hmodels⟩ :=
    exists_actual_AD_uniform_precision_area_models hn hnd μ hAD
  have hK1 : 1 ≤ nativeSurfaceADConstant n c C := by
    have hCnonneg : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    have hinv : 0 ≤ (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n).toReal⁻¹ :=
      inv_nonneg.mpr ENNReal.toReal_nonneg
    dsimp only [nativeSurfaceADConstant]
    linarith
  refine ⟨Ktop, hKtop, nativeSurfaceADConstant n c C, hK1, ?_⟩
  intro ε hε hεfine hsmall R hR k z hcore
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, f, hmodel, hembed, htop, hupper, hlower⟩ :=
    hmodels ε hε (by linarith) (by linarith) R hR k z hcore
  obtain ⟨hreg, hs, hADν, hdiam, _, hg, hl, hplanes⟩ :=
    active_region_native_surface_geometry hn μ R hR k z Good S hS ε hε hεfine hsmall hfit
      f hmodel hembed c C hc hcfin hC hlower hupper
  exact ⟨S, hS, hfit, f, hmodel, htop, hreg, hs, hADν, hdiam, hg, hl, hplanes⟩

end

end RieszRectifiability

end OAI
