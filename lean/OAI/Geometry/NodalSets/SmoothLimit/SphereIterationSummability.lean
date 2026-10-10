import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientNormConvergence

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter
open scoped ContDiff Topology
noncomputable section

theorem sphere_coefficient_diagonal_summable (P : Finset Base) (d : ℕ → SphereEnergyData)
    (hd : ∀ k, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (d k).density)
    (hstep : ∀ k, sphereCoefficientDistance P (k+1) (d k).tensor (d k).density
      (d (k+1)).tensor (d (k+1)).density < (1/2:ℝ)^(k+1)) :
    ∀ J : ℕ, Summable (fun k ↦ sphereCoefficientDistance P J (d k).tensor (d k).density
      (d (k+1)).tensor (d (k+1)).density) := by
  intro J
  have hgeom : Summable (fun k : ℕ ↦ (1/2:ℝ)^(k+1)) :=
    summable_geometric_two.comp_injective (fun _ _ h ↦ Nat.succ.inj h)
  apply Summable.of_norm_bounded_eventually hgeom
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop J] with k hk
  have hnonneg := sphereCoefficientDistance_nonneg P J (d k).tensor (d (k+1)).tensor
    (d k).density (d (k+1)).density
    (fun p _ ↦ intrinsic_coefficient_chart_smooth (d k).tensor (d k).smooth (d k).symm (d k).pos (d k).density (hd k) p)
    (fun p _ ↦ intrinsic_coefficient_chart_smooth (d (k+1)).tensor (d (k+1)).smooth (d (k+1)).symm (d (k+1)).pos
      (d (k+1)).density (hd (k+1)) p)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  exact (sphereCoefficientDistance_mono_order P (d k) (d (k+1)) (hd k) (hd (k+1)) J (k+1) (by omega)).trans (hstep k).le

end
end Yau.Target

end OAI
