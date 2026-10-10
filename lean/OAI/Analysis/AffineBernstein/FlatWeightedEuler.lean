import Mathlib
import OAI.Analysis.AffineBernstein.FlatEulerCore
import OAI.Analysis.AffineBernstein.FlatBlockCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem flatWeightedBlockEuler {W : Set E} (hW : IsOpen W)
    (f g a b : E → ℝ) (v : ι → E) (w : κ → E)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (ha : ContDiffOn ℝ ∞ a W) (hb : ContDiffOn ℝ ∞ b W)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, flatTestContraction (fun i j y => a y * (flatBlockHessian f v y).adjugate i j) v η x +
        flatTestContraction (fun i j y => b y * (flatBlockHessian g w y).adjugate i j) w η x ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    (∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) a) x) +
      (∑ j, ∑ i, (flatBlockHessian g w x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) b) x) = 0 := by
  have hF (y : E) (hy : y ∈ W) (i j : ι) :
      ContDiffAt ℝ ∞ (fun y => (flatBlockHessian f v y).adjugate i j) y :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian (hf.contDiffAt (hW.mem_nhds hy)) v) i j
  have hG (y : E) (hy : y ∈ W) (i j : κ) :
      ContDiffAt ℝ ∞ (fun y => (flatBlockHessian g w y).adjugate i j) y :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian (hg.contDiffAt (hW.mem_nhds hy)) w) i j
  have hp := flatDoubleDivergence_eq_zero_of_stationary hW _ _ v w
    (fun i j y hy => (ha.contDiffAt (hW.mem_nhds hy)).mul (hF y hy i j))
    (fun i j y hy => (hb.contDiffAt (hW.mem_nhds hy)).mul (hG y hy i j)) hstat hx
  change (∑ j, ∑ i, dirDeriv (v j) (dirDeriv (v i)
      (fun y => a y * (flatBlockHessian f v y).adjugate i j)) x) +
    (∑ j, ∑ i, dirDeriv (w j) (dirDeriv (w i)
      (fun y => b y * (flatBlockHessian g w y).adjugate i j)) x) = 0 at hp
  rw [double_divergence_weighted hW (fun y => (flatBlockHessian f v y).adjugate) a v hF
    (fun y hy => ha.contDiffAt (hW.mem_nhds hy))
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hf v hy i).1)
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hf v hy i).2) hx,
    double_divergence_weighted hW (fun y => (flatBlockHessian g w y).adjugate) b w hG
    (fun y hy => hb.contDiffAt (hW.mem_nhds hy))
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hg w hy i).1)
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hg w hy i).2) hx] at hp
  exact hp

end AffineBernstein
end

end OAI
