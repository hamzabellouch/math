import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenFlow
import OAI.Combinatorics.UniformKServer.KeySizeTracker

namespace OAI

                                       
section

/-! The entropy size tracker instantiated by true finite hidden-count data.
Its drift estimate is conditional L1 contraction, never event-conditional. -/
noncomputable section
namespace UniformKServer.KeySizePosterior
open Finset ConditionalLaw RankTracking KeySizeTracker
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {k : ℕ}

def input (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) : KeySizeTracker.Input Ω (k+1) where
  weight := D.weight
  nonneg := fun ω => (D.positive ω).le
  total := D.total
  filtration := D.filtration
  refines := D.refines
  size := fun t ω => 1+posterior D.weight (D.filtration t) (N t) ω
  filtered := fun t ω => 1+posterior D.weight (D.filtration t) (N (t-1)) ω
  range := by
    intro t ω
    have hn := posterior_nonneg (fun v => (D.positive v).le) (fun v => (hN t v).1) (D.filtration t) ω
    have hu : posterior D.weight (D.filtration t) (N t) ω ≤ k := by
      unfold posterior
      calc
        _ ≤ ∑ v, kernel D.weight (D.filtration t) ω v*(k:ℝ) := sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hN t v).2 (kernel_nonneg (fun x => (D.positive x).le) _ _ _)
        _ = _ := by rw [←sum_mul,HiddenFlow.normalization D,one_mul]
    constructor <;> linarith
  measurable := by
    intro t ω v hv
    dsimp only
    rw [posterior_measurable _ _ _ ω v hv]
  filtering := by
    intro t a ha
    have hf := ConditionalLaw.filtering (fun v => (D.positive v).le) (D.filtration t)
      (D.filtration (t+1)) (D.refines t) a (N t) ha
    simpa only [Nat.add_sub_cancel,add_sub_add_left_eq_sub,average,mul_assoc] using hf

theorem drift (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) (t : ℕ) :
    average D.weight (fun ω => |(input D N hN).size (t+1) ω-(input D N hN).filtered (t+1) ω|) ≤
    average D.weight (fun ω => |N (t+1) ω-N t ω|) := by
  simpa only [input,Nat.add_sub_cancel,add_sub_add_left_eq_sub,average] using
    expected_contraction (fun v => (D.positive v).le) (D.filtration (t+1)) (N (t+1)) (N t)

theorem budget (D : HiddenFlow.Data X Ω k) (N : ℕ → Ω → ℝ)
    (hN : ∀ t ω, N t ω ∈ Set.Icc 0 (k:ℝ)) (H : ℕ) :
    (∑ t ∈ range H, average D.weight (KeySizeTracker.charge (input D N hN) t)) ≤
      144*ell (k+1)*(∑ t ∈ range H, average D.weight (fun ω => |N (t+1) ω-N t ω|))+
      288*(k+1)*(1+ell (k+1)) := by
  have hk : (1:ℝ) ≤ k+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he : 0 ≤ ell (k+1) := by unfold ell; linarith [Real.log_nonneg hk]
  have hb := KeySizeTracker.budget (input D N hN) hk H
  have hd := sum_le_sum (fun t (_ : t ∈ range H) => drift D N hN t)
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 144*ell (k+1) by positivity)
  exact hb.trans (add_le_add hm (le_refl _))

end UniformKServer.KeySizePosterior

end


end

end OAI
