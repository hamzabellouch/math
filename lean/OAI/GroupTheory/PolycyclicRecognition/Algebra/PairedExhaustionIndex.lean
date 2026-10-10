import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionIndexBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeCyclicExtension

namespace OAI

/-! # Uniform finite-index refinements survive an increasing union -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finiteIndex_iSup_of_paired_exhaustions (S K : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n) (c : ℕ)
    (hfinite : ∀ n, ((K n).subgroupOf (S n)).FiniteIndex)
    (hbound : ∀ n, ((K n).subgroupOf (S n)).index ≤ c) :
    (⨆ n, K n).FiniteIndex := by
  apply finiteIndex_of_exhaustion_index_bound S hS hcover (⨆ n, K n) c
  · intro n
    let := hfinite n
    exact Subgroup.finiteIndex_of_le
      (show (K n).subgroupOf (S n) ≤ (⨆ n, K n).subgroupOf (S n) from
        fun _ hx => (le_iSup K n) hx)
  · intro n
    exact (Subgroup.relIndex_le_of_le_left (le_iSup K n)
      (hfinite n).index_ne_zero).trans (hbound n)

theorem torsionFree_iSup_of_monotone (K : ℕ → Subgroup G) (hK : Monotone K)
    (htf : ∀ n, HasNoNontrivialTorsion (K n)) :
    HasNoNontrivialTorsion (⨆ n, K n : Subgroup G) := by
  have hdir : Directed (· ≤ ·) K :=
    fun n m => ⟨max n m, hK (le_max_left _ _), hK (le_max_right _ _)⟩
  intro g k hk hg
  obtain ⟨n, hn⟩ := (Subgroup.mem_iSup_of_directed hdir).mp g.property
  have hpow : (⟨(g : G), hn⟩ : K n) ^ k = 1 :=
    Subtype.ext (congrArg (fun x : (⨆ n, K n : Subgroup G) => (x : G)) hg)
  exact Subtype.ext (congrArg (fun x : K n => (x : G)) (htf n ⟨g, hn⟩ k hk hpow))

end PolycyclicRecognition

end

end OAI
