import OAI.Analysis.CircleDomains.Selection.ReversedTags
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Actual first-exit cuts for the collar-splicing construction. Every
retained initial fragment lies in the corresponding closed collar disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def firstExitTime (γ : C(PathTime, X)) (V : Set X) : PathTime :=
  sInf {t | γ t ∉ V}

theorem firstExitTime_le (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : γ t ∉ V) : firstExitTime γ V ≤ t :=
  sInf_le ht

theorem mem_before_firstExit (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : t < firstExitTime γ V) : γ t ∈ V := by
  by_contra hn
  exact ht.not_ge (firstExitTime_le γ V hn)

theorem firstExit_notMem (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∉ V := by
  exact (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem ⟨⊤, hend⟩

theorem firstExit_pos (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : ⊥ < firstExitTime γ V := by
  apply bot_lt_iff_ne_bot.mpr
  intro he
  exact firstExit_notMem γ hV hend (he ▸ hstart)

theorem firstExit_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∈ frontier V := by
  have hpos := firstExit_pos γ hV hstart hend
  have hcl : firstExitTime γ V ∈ closure (Iio (firstExitTime γ V)) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : firstExitTime γ V ≤ firstExitTime γ V)
  have hmap : MapsTo γ (Iio (firstExitTime γ V)) V := fun _ ht => mem_before_firstExit γ V ht
  rw [frontier, hV.interior_eq]
  exact ⟨hmap.closure γ.continuous hcl, firstExit_notMem γ hV hend⟩

theorem firstExit_initial_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) :
    MapsTo γ (Iic (firstExitTime γ V)) (closure V) := by
  intro t ht
  change t ≤ firstExitTime γ V at ht
  rcases ht.eq_or_lt with rfl | hlt
  · exact frontier_subset_closure (firstExit_frontier γ hV hstart hend)
  · exact subset_closure (mem_before_firstExit γ V hlt)

theorem firstExit_nested (γ : C(PathTime, X)) {V W : Set X}
    (hW : IsOpen W) (hVW : V ⊆ W) (hend : γ ⊤ ∉ W) :
    firstExitTime γ V ≤ firstExitTime γ W := by
  apply firstExitTime_le
  exact fun h => firstExit_notMem γ hW hend (hVW h)

theorem firstExit_strict_nested (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ W) :
    firstExitTime γ V < firstExitTime γ W := by
  have hsub : V ⊆ W := subset_closure.trans hVW
  have hvend : γ ⊤ ∉ V := fun h => hend (hsub h)
  apply lt_of_le_of_ne (firstExit_nested γ hW hsub hend)
  intro he
  have hv := hVW (frontier_subset_closure (firstExit_frontier γ hV hstart hvend))
  rw [he] at hv
  exact firstExit_notMem γ hW hend hv

end CircleDomainRigidity

end

end OAI
