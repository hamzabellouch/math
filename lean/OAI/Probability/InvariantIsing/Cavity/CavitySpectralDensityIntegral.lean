import OAI.Probability.InvariantIsing.Cavity.CavityFieldResidual
import OAI.Probability.InvariantIsing.Spectral.SpectralDensityContinuity
import OAI.Probability.InvariantIsing.Spectral.SpectralPrimitive

namespace OAI

/-! Integrals of the spectral-group density on the root interval,
finite overlap gaps, and ordinary terminal residual. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma integral_spectralPathDensity_root (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ᵐ s ∂pathMeasure, q ≤ p s) :
    (∫ r in 0..q, spectralPathDensity rho lam hrho hsum p a r) =
      q * projectedResolventDerivative rho lam hrho hsum a (deficit p q) := by
  calc
    _ = ∫ _r in 0..q,
        projectedResolventDerivative rho lam hrho hsum a (deficit p q) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hq
      intro r hr
      dsimp only [spectralPathDensity]
      rw [deficit_constant_below_ae_lower p hbound hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

lemma integral_spectralPathDensity_gap (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {u v : ℝ} (huv : u < v)
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ u ∨ v ≤ p s)
    (hpos : 0 < deficit p v) (hmass : pathMeasure.real {s | p s ≤ u} ≠ 0) :
    (∫ r in u..v, spectralPathDensity rho lam hrho hsum p a r) =
      (projectedResolvent rho lam hrho hsum a (deficit p u) -
        projectedResolvent rho lam hrho hsum a (deficit p v)) /
          pathMeasure.real {s | p s ≤ u} := by
  let F := projectedResolvent rho lam hrho hsum a
  let ζ := pathMeasure.real {s | p s ≤ u}
  have hp (r : ℝ) (hr : r ∈ Icc u v) : 0 < deficit p r :=
    hpos.trans_le (deficit_antitone_argument p hr.2)
  have hc : ContinuousOn (fun r => F (deficit p r)) (Icc u v) := by
    intro r hr
    exact (((hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (hp r hr)).hasDerivAt.continuousAt).comp
        (continuous_deficit p).continuousAt).continuousWithinAt
  have hd : ∀ r ∈ Ioo u v, HasDerivAt (fun r => F (deficit p r))
      ((-ζ) * spectralPathDensity rho lam hrho hsum p a r) r := by
    intro r hr
    have hF := (hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (hp r ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
    have hD := hasDerivAt_deficit_on_gap p hgap hr
    convert hF.comp r hD using 1 <;>
      simp only [F, Function.comp_def, ζ, spectralPathDensity]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv.le hc hd
    (((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable u v).const_mul (-ζ))
  rw [intervalIntegral.integral_const_mul] at hf
  apply (eq_div_iff hmass).mpr
  change (∫ r in u..v, spectralPathDensity rho lam hrho hsum p a r) * ζ =
    F (deficit p u) - F (deficit p v)
  linarith

lemma integral_spectralPathDensity_tail (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (a : ι) {top : ℝ} (htop : top ≤ 1)
    (hbound : ∀ᵐ s ∂pathMeasure, p s ≤ top) :
    (∫ r in top..1, spectralPathDensity rho lam hrho hsum p a r) =
      projectedResolvent rho lam hrho hsum a (deficit p top) := by
  let F := projectedResolvent rho lam hrho hsum a
  have he (r : ℝ) (hr : r ∈ Icc top 1) : deficit p r = 1 - r :=
    deficit_eq_one_sub_of_ae_le p (hbound.mono (fun _ hs => hs.trans hr.1))
  have hc : ContinuousOn (fun r => F (1 - r)) (Icc top 1) :=
    (continuousOn_projectedResolvent rho lam hrho hsum a).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun _ hr => ⟨sub_nonneg.mpr hr.2, sub_le_sub_left hr.1 1⟩)
  have hd : ∀ r ∈ Ioo top 1, HasDerivAt (fun r => F (1 - r))
      (-spectralPathDensity rho lam hrho hsum p a r) r := by
    intro r hr
    have hF := (hasStrictDerivAt_projectedResolvent rho lam hrho hsum a
      (sub_pos.mpr hr.2)).hasDerivAt
    convert hF.comp r ((hasDerivAt_id r).const_sub 1) using 1 <;>
      simp only [F, Function.comp_def, spectralPathDensity, he r ⟨hr.1.le, hr.2.le⟩]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htop hc hd
    (((continuous_spectralPathDensity rho lam hrho hsum p a).intervalIntegrable top 1).neg)
  rw [intervalIntegral.integral_neg] at hf
  change -(∫ r in top..1, spectralPathDensity rho lam hrho hsum p a r) =
    F (1 - 1) - F (1 - top) at hf
  rw [sub_self, show F 0 = 0 by simp [F, projectedResolvent]] at hf
  rw [deficit_eq_one_sub_of_ae_le p hbound]
  linarith

end InvariantIsing

end

end OAI
