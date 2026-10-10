import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionGlobalLipschitz
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaces

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (s : ℕ)

def activeRegionTransitionMap : ℕ → Ambient d → Ambient d
  | 0 => id
  | j + 1 => activeLevelProjectionMap μ R hR k z Good (s + j + 1) S hS ∘ activeRegionTransitionMap j

theorem activeRegionParameterMap_add (j : ℕ) (u : Ambient d) :
    activeRegionParameterMap μ R hR k z Good S hS (s + j) u =
      activeRegionTransitionMap μ R hR k z Good S hS s j
        (activeRegionParameterMap μ R hR k z Good S hS s u) := by
  induction j with
  | zero => simp only [Nat.add_zero, activeRegionTransitionMap, id_eq]
  | succ j ih =>
    rw [← Nat.add_assoc, activeRegionParameterMap, activeRegionTransitionMap, Function.comp_apply,
      Function.comp_apply, ih]

theorem activeRegionSurface_add (j : ℕ) :
    activeRegionSurface μ R hR k z Good S hS (s + j) =
      (activeRegionTransitionMap μ R hR k z Good S hS s j) ''
        activeRegionSurface μ R hR k z Good S hS s := by
  induction j with
  | zero => simp only [Nat.add_zero, activeRegionTransitionMap, Set.image_id]
  | succ j ih =>
    rw [← Nat.add_assoc, activeRegionSurface, ih, Set.image_image]
    rfl

theorem activeRegionTransitionMap_global_lipschitz (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) (j : ℕ) :
    LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ j)
      (activeRegionTransitionMap μ R hR k z Good S hS s j) := by
  induction j with
  | zero =>
    rw [pow_zero]
    apply LipschitzWith.mk_one
    intro x y
    rfl
  | succ j ih =>
    have hstep := activeLevelProjectionMap_global_lipschitz μ R hR k z Good (s + j + 1)
      S hS ε hεsmall
      (fun i hi => hfit i ((mem_activeLevelIndex μ R hR k z Good (s + j + 1) i).mp hi).2)
    simpa only [activeRegionTransitionMap, pow_succ'] using! hstep.comp ih

end

end RieszRectifiability

end OAI
