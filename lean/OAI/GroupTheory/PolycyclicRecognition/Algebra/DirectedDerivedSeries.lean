import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocallyBoundedDerivedSeries

namespace OAI

/-! # Directed unions with uniformly bounded derived series -/
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

def directedDerivedSeries (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) : Subgroup G where
  carrier := {g | ∃ H ∈ C, g ∈ ambientDerivedSeries H n}
  one_mem' := by
    obtain ⟨H, hH⟩ := hne
    exact ⟨H, hH, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨H, hH, hx⟩ ⟨K, hK, hy⟩
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    exact ⟨L, hL, Subgroup.mul_mem _
      (ambientDerivedSeries_mono hHL n hx) (ambientDerivedSeries_mono hKL n hy)⟩
  inv_mem' := by
    rintro x ⟨H, hH, hx⟩
    exact ⟨H, hH, Subgroup.inv_mem _ hx⟩

theorem sSup_ambientDerivedSeries_le_directed (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) :
    ambientDerivedSeries (sSup C) n ≤ directedDerivedSeries C hne hdir n := by
  induction n with
  | zero =>
    rw [ambientDerivedSeries_zero]
    intro g hg
    obtain ⟨H, hH, hg⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp hg
    exact ⟨H, hH, by rwa [ambientDerivedSeries_zero]⟩
  | succ n ih =>
    rw [ambientDerivedSeries_succ]
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨H, hH, hxH⟩ := ih hx
    obtain ⟨K, hK, hyK⟩ := ih hy
    obtain ⟨L, hL, hHL, hKL⟩ := hdir H hH K hK
    refine ⟨L, hL, ?_⟩
    rw [ambientDerivedSeries_succ]
    exact Subgroup.commutator_mem_commutator
      (ambientDerivedSeries_mono hHL n hxH) (ambientDerivedSeries_mono hKL n hyK)

theorem sSup_derivedSeries_eq_bot (C : Set (Subgroup G)) (hne : C.Nonempty)
    (hdir : DirectedOn (· ≤ ·) C) (n : ℕ) (hn : ∀ H ∈ C, derivedSeries H n = ⊥) :
    derivedSeries (sSup C : Subgroup G) n = ⊥ := by
  apply Subgroup.map_injective (f := (sSup C).subtype) Subtype.val_injective
  rw [Subgroup.map_bot]
  apply eq_bot_iff.mpr
  intro g hg
  obtain ⟨H, hH, hgH⟩ := sSup_ambientDerivedSeries_le_directed C hne hdir n hg
  simpa only [ambientDerivedSeries, hn H hH, Subgroup.map_bot] using hgH

end PolycyclicRecognition

end OAI
