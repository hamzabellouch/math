import OAI.Analysis.CircleDomains.Topology.CurveLowerDistance
import OAI.Analysis.CircleDomains.Sobolev.LineDerivativeLocality
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.Jacobian

namespace OAI

/-! A planar curve approximated by a linear map on an arbitrary real set
has the same derivative bound almost everywhere on that set. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma ae_curve_derivative_sub_le {γ : ℝ → ℂ} {A : ℝ →L[ℝ] ℂ}
    {S : Set ℝ} {δ : ℝ≥0} (ha : ApproximatesLinearOn γ A S δ)
    {d : ℝ → ℝ →L[ℝ] ℂ} :
    ∀ᵐ x ∂volume, x ∈ S → HasFDerivWithinAt γ (d x) S x → ‖d x-A‖ ≤ δ := by
  have hnull : volume {x ∈ S | 𝓝[S ∩ Ioi x] x = ⊥} = 0 :=
    countable_setOfPred_isolated_right_within.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxS hd
  let : NeBot (𝓝[S ∩ Ioi x] x) := ⟨fun hbot => hx ⟨hxS, hbot⟩⟩
  have hh : HasDerivWithinAt (γ-(A : ℝ → ℂ)) ((d x-A) 1) S x :=
    (hd.sub A.hasFDerivAt.hasFDerivWithinAt).hasDerivWithinAt
  have hl : Tendsto (fun y => ‖slope (γ-(A : ℝ → ℂ)) x y‖)
      (𝓝[S ∩ Ioi x] x) (𝓝 ‖(d x-A) 1‖) :=
    (hasDerivWithinAt_iff_tendsto_slope.mp hh).norm.mono_left
      (nhdsWithin_mono _ (fun y hy => ⟨hy.1, ne_of_gt hy.2⟩))
  have hbound : ∀ᶠ y in 𝓝[S ∩ Ioi x] x, ‖slope (γ-(A : ℝ → ℂ)) x y‖ ≤ (δ:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hdist := ha.lipschitzOnWith.dist_le_mul y hy.1 x hxS
    rw [dist_eq_norm, Real.dist_eq] at hdist
    rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
    apply (inv_mul_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hy.2)))).mpr
    simpa only [vsub_eq_sub, mul_comm] using hdist
  have hb := le_of_tendsto hl hbound
  simpa only [norm_real_clm_apply, abs_one, mul_one] using hb

end CircleDomainRigidity

end

end OAI
