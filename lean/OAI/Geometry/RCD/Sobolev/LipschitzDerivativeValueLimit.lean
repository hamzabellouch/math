import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

namespace OAI

/-! # Identifying a derivative limit from common local Lipschitz bounds -/

open Set Filter
open scoped Topology NNReal UniformConvergence
noncomputable section
namespace RegularPointCoordinates

theorem uniform_limit_of_common_lipschitz (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (L : ℝ≥0) {a b : ℝ}
    (hL : ∀ k, LipschitzOnWith L (F k) (Icc a b))
    (hf : ∀ x ∈ Icc a b, Tendsto (fun k => F k x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop (Icc a b) := by
  let Fr k (x : Icc a b) := F k x
  let fr (x : Icc a b) := f x
  have he : Equicontinuous Fr :=
    (LipschitzWith.uniformEquicontinuous Fr L (fun k => (hL k).to_restrict)).equicontinuous
  have hp : Tendsto Fr atTop (𝓝 fr) := tendsto_pi_nhds.mpr fun x => hf x x.property
  have hu := (he.tendsto_uniformFun_iff_pi atTop fr).mpr hp
  exact tendstoUniformlyOn_iff_restrict.mpr (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

theorem hasDerivAt_of_common_lipschitz_derivatives
    (F : ℕ → ℝ → ℝ) (f v : ℝ → ℝ) (L : ℝ≥0) {a b t : ℝ}
    (hL : ∀ k, LipschitzOnWith L (deriv (F k)) (Icc a b))
    (hF : ∀ k x, x ∈ Ioo a b → DifferentiableAt ℝ (F k) x)
    (hf : ∀ x ∈ Ioo a b, Tendsto (fun k => F k x) atTop (𝓝 (f x)))
    (hv : ∀ x ∈ Icc a b, Tendsto (fun k => deriv (F k) x) atTop (𝓝 (v x)))
    (ht : t ∈ Ioo a b) : HasDerivAt f (v t) t := by
  have hu := uniform_limit_of_common_lipschitz (fun k => deriv (F k)) v L hL hv
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hu.mono Ioo_subset_Icc_self)
    (Eventually.of_forall fun k x hx => (hF k x hx).hasDerivAt) hf ht

end RegularPointCoordinates

end

end OAI
