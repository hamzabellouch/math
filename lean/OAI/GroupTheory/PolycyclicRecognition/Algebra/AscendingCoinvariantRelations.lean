import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingQuotientColimit
import Mathlib.RepresentationTheory.Coinvariants

namespace OAI

/-! # Coinvariant relations are detected in a finite subgroup stage

For an ascending exhaustion of a group, a linear combination of coinvariant
relations uses only finitely many group elements. It therefore already lies
in the relations of one stage of the exhaustion.
-/
noncomputable section
namespace PolycyclicRecognition
open Representation
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℤ V]
variable (ρ : Representation ℤ K V)

abbrev subgroupCoinvariantRelations (H : Subgroup K) : Submodule ℤ V :=
  Coinvariants.ker (ρ.comp H.subtype)

theorem subgroupCoinvariantRelations_mono {H J : Subgroup K} (h : H ≤ J) :
    subgroupCoinvariantRelations ρ H ≤ subgroupCoinvariantRelations ρ J := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨g, v⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp J.subtype) ⟨g.val, h g.property⟩ v

theorem subgroupCoinvariantRelations_le (H : Subgroup K) :
    subgroupCoinvariantRelations ρ H ≤ Coinvariants.ker ρ := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨g, v⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ) g.val v

theorem subgroupCoinvariantRelations_exhaustion (H : ℕ → Subgroup K) (S : Subgroup K)
    (hmono : Monotone H) (hcover : ∀ g ∈ S, ∃ n, g ∈ H n)
    {v : V} (hv : v ∈ subgroupCoinvariantRelations ρ S) :
    ∃ n, v ∈ subgroupCoinvariantRelations ρ (H n) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hcover g.val g.property
    exact ⟨n, Coinvariants.sub_mem_ker (ρ := ρ.comp (H n).subtype) ⟨g.val, hn⟩ v⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨max i j, Submodule.add_mem _
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_left _ _)) hi)
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_right _ _)) hj)⟩
  | smul r x _ hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Submodule.smul_mem _ r hn⟩

theorem coinvariantRelations_exhaustion (H : ℕ → Subgroup K) (hmono : Monotone H)
    (hcover : ∀ g : K, ∃ n, g ∈ H n) {v : V} (hv : v ∈ Coinvariants.ker ρ) :
    ∃ n, v ∈ subgroupCoinvariantRelations ρ (H n) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g, v⟩, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hcover g
    exact ⟨n, Coinvariants.sub_mem_ker (ρ := ρ.comp (H n).subtype) ⟨g, hn⟩ v⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨max i j, Submodule.add_mem _
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_left _ _)) hi)
      (subgroupCoinvariantRelations_mono ρ (hmono (Nat.le_max_right _ _)) hj)⟩
  | smul r x _ hx =>
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Submodule.smul_mem _ r hn⟩

end PolycyclicRecognition

end

end OAI
