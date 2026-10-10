import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.NativeSurfaceStopCoverage
import OAI.Analysis.RieszRectifiability.Surfaces.NativeCoreAreaFraction
import OAI.Analysis.RieszRectifiability.Foundations.FiniteMassSurvival

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem projection_region_original_area_contraction {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖)
    (hcover : closedBall (T z) (latticeRadius R k / 32) ⊆
      T '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)))
    (hsmall : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G) :
    let Good := cellProjectionNoncollapse S P κ
    ENNReal.ofReal (nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
      ν (cellRegionLimit ν R hR k z Good) ∧
      (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
        ENNReal.ofReal (1 - nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) := by
  let Good := cellProjectionNoncollapse S P κ
  have hTlip : LipschitzWith 1 T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hT _
  have hproj := native_surface_core_disk_le_survivor_add_shadow ν A hν hsupport
    C G hC hG hg hlower R hR k z Good T hTlip hcover
  have hshadow := projection_conditioned_stopping_shadow_le_top ν C G hC hG hg hlower
    R hR k hcore z S hS hcenter P σ κ hσ hκ hwidth hfit T hT hnorm
  have hshadow' := hshadow.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hsmall) le_rfl)
  have hdisk := native_core_disk_area_ge_double_fraction ν G hG hg R hR k z (T z)
  have hbound := hdisk.trans (hproj.trans (add_le_add le_rfl hshadow'))
  have hfinite : ν (cleanSupportCell ν R hR k z) ≠ ⊤ :=
    (cleanSupportCell_measure_pos_finite ν C G hC hG hg hlower R hR k hcore z).2.ne
  have harea : ν (cellRegionLimit ν R hR k z Good) ≤ ν (cleanSupportCell ν R hR k z) :=
    measure_mono (fun _ hx => hx.1)
  have hθ := nativeCoreAreaFraction_pos_le_half n G hG
  have hretain := retained_mass_ge_of_double_fraction hfinite harea (nativeCoreAreaFraction n G) hθ.1.le hbound
  exact ⟨hretain, cellRegion_stopping_mass_contraction ν R hR k z Good hfinite
    (nativeCoreAreaFraction n G) hθ.1.le (by linarith [hθ.2]) hretain⟩

end

end RieszRectifiability

end OAI
