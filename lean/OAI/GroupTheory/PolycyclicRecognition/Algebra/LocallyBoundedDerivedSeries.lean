import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift
import Mathlib.GroupTheory.Solvable

namespace OAI

/-! # A uniform derived-series bound passes from finitely generated subgroups -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

def ambientDerivedSeries (H : Subgroup G) (n : ℕ) : Subgroup G :=
  (derivedSeries H n).map H.subtype

theorem ambientDerivedSeries_mono {H K : Subgroup G} (hHK : H ≤ K) (n : ℕ) :
    ambientDerivedSeries H n ≤ ambientDerivedSeries K n := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := hx
  refine ⟨Subgroup.inclusion hHK h, ?_, rfl⟩
  exact map_derivedSeries_le_derivedSeries (Subgroup.inclusion hHK) n ⟨h, hh, rfl⟩

theorem ambientDerivedSeries_zero (H : Subgroup G) : ambientDerivedSeries H 0 = H := by
  simp only [ambientDerivedSeries, derivedSeries_zero, Subgroup.map_top, Subgroup.range_subtype]

theorem ambientDerivedSeries_succ (H : Subgroup G) (n : ℕ) :
    ambientDerivedSeries H (n + 1) = ⁅ambientDerivedSeries H n, ambientDerivedSeries H n⁆ := by
  simp only [ambientDerivedSeries, derivedSeries_succ, Subgroup.map_commutator]

def fgDerivedSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H : Subgroup G, H.FG ∧ g ∈ ambientDerivedSeries H n}
  one_mem' := ⟨⊥, Subgroup.FG.bot, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    exact ⟨H ⊔ K, hH.sup hK, Subgroup.mul_mem _
      (ambientDerivedSeries_mono le_sup_left n hx)
      (ambientDerivedSeries_mono le_sup_right n hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

theorem derivedSeries_le_fgDerivedSubgroup (n : ℕ) :
    derivedSeries G n ≤ fgDerivedSubgroup n := by
  induction n with
  | zero =>
    intro g _
    let H : Subgroup G := Subgroup.closure {g}
    have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨{g}, rfl, Set.finite_singleton g⟩
    refine ⟨H, hH, ?_⟩
    rw [ambientDerivedSeries_zero]
    exact Subgroup.subset_closure (Set.mem_singleton g)
  | succ n ih =>
    rw [derivedSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := ih hy
    refine ⟨H ⊔ K, hH.sup hK, ?_⟩
    rw [ambientDerivedSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (ambientDerivedSeries_mono le_sup_left n hxH)
      (ambientDerivedSeries_mono le_sup_right n hyK)

theorem derivedSeries_eq_bot_of_fg_subgroups (n : ℕ)
    (h : ∀ H : Subgroup G, H.FG → derivedSeries H n = ⊥) : derivedSeries G n = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := derivedSeries_le_fgDerivedSubgroup n hg
  simpa only [ambientDerivedSeries, h H hH, Subgroup.map_bot] using hgH

end PolycyclicRecognition

end

end OAI
