import OAI.NumberTheory.DukePrimeDegree.Dynamics.NormalizerInvariantSigma
import Mathlib.GroupTheory.FreeGroup.Basic

namespace OAI

/-!
# A dense countable subgroup preserved by one normalizer

Starting with a countable dense set, add all its integer conjugates by
the chosen normalizer and generate a subgroup. This keeps countability
and density while ensuring that the same invariant sigma algebra is
available for both ergodic decomposition and normalizer covariance.
-/

noncomputable section
open Set
open scoped Topology

namespace DukePrimeDegree

private def integerConjugates {G : Type*} [Group G] (a : G) (s : Set G) : Set G :=
  Set.range (fun p : ℤ × s => a ^ p.1 * p.2.val * a ^ (-p.1))

private lemma integerConjugates_normalizer {G : Type*} [Group G]
    (a : G) (s : Set G) : a ∈ Subgroup.normalizer (integerConjugates a s) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  ext g
  constructor
  · rintro ⟨h, ⟨⟨z, x⟩, rfl⟩, rfl⟩
    refine ⟨(z + 1, x), ?_⟩
    simp only [MulAut.conj_apply, zpow_add, zpow_one, neg_add_rev, zpow_neg]
    group
  · rintro ⟨⟨z, x⟩, rfl⟩
    refine ⟨a ^ (z - 1) * x.val * a ^ (-(z - 1)), ⟨(z - 1, x), rfl⟩, ?_⟩
    simp only [MulAut.conj_apply, zpow_sub, zpow_one, zpow_neg]
    group

/-- An actual ambient normalizer can be retained when passing to a
countable dense subgroup of a given topological subgroup. -/
theorem exists_countable_dense_normalized_subgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) [TopologicalSpace.SeparableSpace H]
    (a : G) (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    ∃ (S : Subgroup G) (hSH : S ≤ H), Countable S ∧
      DenseRange (fun h : S => (⟨h.val, hSH h.property⟩ : H)) ∧
      a ∈ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense H
  let sG : Set G := (fun h : H => (h : G)) '' s
  have hsG : sG.Countable := hs.image _
  let C := integerConjugates a sG
  let S : Subgroup G := Subgroup.closure C
  have hSH : S ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro g ⟨⟨z, x⟩, rfl⟩
    obtain ⟨h, _hs, hh⟩ := x.property
    have hpower : a ^ z ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).zpow_mem ha z
    have hmem := (Subgroup.mem_normalizer_iff.mp hpower h.val).mp h.property
    change a ^ z * x.val * a ^ (-z) ∈ H
    rw [zpow_neg, ← hh]
    exact hmem
  have hC : C.Countable := by
    let : Countable sG := hsG.to_subtype
    exact Set.countable_range _
  have hS : Countable S := by
    let : Countable C := hC.to_subtype
    have hcount : (Set.range (FreeGroup.lift ((↑) : C → G))).Countable :=
      Set.countable_range _
    have hcount' : (S : Set G).Countable := by
      simpa only [S, FreeGroup.closure_eq_range, MonoidHom.coe_range] using hcount
    exact hcount'.to_subtype
  refine ⟨S, hSH, hS, ?_, ?_⟩
  · apply hdense.mono
    intro h hh
    have hsGmem : h.val ∈ sG := ⟨h, hh, rfl⟩
    have hmem : h.val ∈ S := by
      apply Subgroup.subset_closure
      exact ⟨(0, ⟨h.val, hsGmem⟩), by simp⟩
    exact ⟨⟨h.val, hmem⟩, Subtype.ext rfl⟩
  · exact Subgroup.normalizer_le_normalizer_closure C
      (integerConjugates_normalizer a sG)

end DukePrimeDegree

end

end OAI
