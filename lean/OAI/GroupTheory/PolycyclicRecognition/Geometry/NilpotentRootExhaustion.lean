import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolycyclicRootIndex
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootGenerators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolyZ
import Mathlib.Basic.Countable.Defs

namespace OAI

/-! # Exhausting a countable nilpotent group by finite-index extensions of a core

Finite integral dimension supplies a finitely generated root core. Every
finitely generated overgroup of that core contains it with finite index.
This gives the directed family needed to compute the kernel's homology.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_finiteIndex (hG : HasFiniteIntegralCohomologicalDimension G)
    (H : Subgroup G) (hH : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (L : Subgroup G) (hL : L.FG) : (H.subgroupOf L).FiniteIndex := by
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  have hp := (nilpotent_polyZ_of_finitelyGenerated_torsionFree
    (hG.subgroup L).torsionFree).isPolycyclic
  apply hp.finiteIndex_of_roots
  intro g
  obtain ⟨n, hn, hg⟩ := hH g
  exact ⟨n, hn, hg⟩

theorem exists_nilpotent_root_exhaustion [Countable G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ H : Subgroup G, H.FG ∧ ∃ S : ℕ → Subgroup G,
      Monotone S ∧ (∀ n, (S n).FG) ∧ (∀ n, H ≤ S n) ∧
      (∀ g, ∃ n, g ∈ S n) ∧ (∀ n, (H.subgroupOf (S n)).FiniteIndex) := by
  classical
  obtain ⟨H, hH, hroot⟩ := nilpotent_exists_fg_subgroup_containing_powers hG
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let T (n : ℕ) : Set G := Set.range (fun i : Fin n => e i)
  let S (n : ℕ) := H ⊔ Subgroup.closure (T n)
  have hS (n : ℕ) : (S n).FG :=
    hH.sup ((Subgroup.fg_iff _).mpr ⟨T n, rfl, Set.finite_range _⟩)
  refine ⟨H, hH, S, ?_, hS, fun _ => le_sup_left, ?_, ?_⟩
  · intro i j hij
    apply sup_le_sup_left
    apply Subgroup.closure_mono
    rintro g ⟨k, rfl⟩
    exact ⟨⟨k, k.isLt.trans_le hij⟩, rfl⟩
  · intro g
    obtain ⟨n, rfl⟩ := he g
    refine ⟨n + 1, (show Subgroup.closure (T (n + 1)) ≤ S (n + 1) from le_sup_right) ?_⟩
    exact Subgroup.subset_closure ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
  · intro n
    exact nilpotent_rootCore_finiteIndex hG H hroot (S n) (hS n)

end PolycyclicRecognition

end

end OAI
