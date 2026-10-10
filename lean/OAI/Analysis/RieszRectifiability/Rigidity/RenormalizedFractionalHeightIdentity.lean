import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.TruncatedRenormalizedHeightIdentity
import OAI.Analysis.RieszRectifiability.Limits.ComplexInteriorCutoffLimit
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalTruncatedHeightLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology SchwartzMap

theorem compact_schwartz_renormalized_height_identity (p : ℕ)
    (a : Ambient (p + 1)) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (w : Ambient (p + 1) → ℝ) (hwm : Measurable w)
    (hw : IntegrableOn w (ball a R) volume)
    (hweight : Integrable (fun x => |w x| * polynomialDecay (p + 3) x) volume)
    (g : 𝓢(Ambient (p + 1), ℂ)) (hzero : (∫ x, g x) = 0)
    (hnear : ∀ x, g x ≠ 0 → dist x a ≤ H)
    (B : ℝ) (hB : 0 ≤ B) (hgB : ∀ x, ‖g x‖ ≤ B)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) volume)
    (hinterior : Integrable (complexHeightInteriorIntegrand (p + 1) w g)
      ((volume.restrict (ball a R)).prod (volume.restrict (ball a R)))) :
    (∫ x, w x • fractionalSchwartzTest p g x) =
      complexHeightPairingOn (p + 1) volume a (ball a R) w g := by
  let ε := fun j : ℕ => (1 / 2 : ℝ) ^ j
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  let N := ∫ q, complexRenormalizedNormalIntegrand (p + 1) w g a q
    ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R)ᶜ)
  let I := fun j => ∫ q : Ambient (p + 1) × Ambient (p + 1),
    (w q.1 - w q.2) • (symmetricFractionalCutoffKernel (p + 1) (ε j) q • (g q.1 - g q.2))
      ∂(volume.restrict (ball a R)).prod (volume.restrict (ball a R))
  have hleft := height_fractional_truncated_integral_tendsto p volume w hwm hweight ε hε g hzero
  have hright : Tendsto (fun j => (1 / 2 : ℝ) • I j + N) atTop
      (𝓝 (complexHeightPairingOn (p + 1) volume a (ball a R) w g)) :=
    ((complex_height_interior_cutoff_integral_tendsto (p + 1)
      (volume.restrict (ball a R)) w g hinterior ε hε).const_smul (1 / 2 : ℝ)).add_const N
  have heq : (fun j => ∫ x, w x • fractionalSchwartzTruncatedTest p (ε j) g x) =ᶠ[atTop]
      fun j => (1 / 2 : ℝ) • I j + N := by
    have hp : 0 < R - H := by linarith
    filter_upwards [hε.eventually (gt_mem_nhds hp)] with j hj
    exact (compact_schwartz_truncated_height_pairing p a H R hH hR hHR (ε j)
      (hεpos j) (by linarith) w hwm hw g hzero hnear B hB hgB hweighted).2
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end

end RieszRectifiability

end OAI
