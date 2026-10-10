import OAI.Probability.SATComputability.RestoredCandidates
import OAI.Probability.SATComputability.PoissonMaskCounts

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped Classical

noncomputable section

local instance maskPermutationsDecidableEq (n : ℕ) : DecidableEq (DeletionCandidate n) :=
  Classical.decEq _

def candidatePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (DeletionCandidate n) where
  toFun x v := x (e.symm v)
  invFun x v := x (e v)
  left_inv x := by funext v; simp
  right_inv x := by funext v; simp

def literalPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (SignedLiteral n) :=
  e.prodCongr (Equiv.refl Bool)

noncomputable def renameMask {n : ℕ} (e : Equiv.Perm (Fin n))
    (U : Finset (DeletionCandidate n)) : Finset (DeletionCandidate n) :=
  U.image (candidatePermutation e)

theorem deletedVariables_permutation {n : ℕ} (e : Equiv.Perm (Fin n)) (x : DeletionCandidate n) :
    deletedVariables (candidatePermutation e x) = (deletedVariables x).image e := by
  ext v
  constructor
  · intro h
    have hx : x (e.symm v) = none := (Finset.mem_filter.mp h).2
    exact Finset.mem_image.mpr ⟨e.symm v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,e.apply_symm_apply v⟩
  · intro h
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp h
    have hx : x w = none := (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change x (e.symm v) = none
    rw [← hwe,Equiv.symm_apply_apply]
    exact hx

theorem deletionBudget_permutation {n r : ℕ} (e : Equiv.Perm (Fin n)) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ deletionBudgetMask n r ↔ x ∈ deletionBudgetMask n r := by
  simp only [deletionBudgetMask, Finset.mem_filter, Finset.mem_univ, true_and,
    deletedVariables_permutation, Finset.card_image_of_injective _ e.injective]

theorem mem_freeDeletionBudgetMask_erase {n r : ℕ} (v : Fin n) (x : DeletionCandidate n) :
    x ∈ freeDeletionBudgetMask n r v ↔ ((deletedVariables x).erase v).card ≤ r := by
  simp only [freeDeletionBudgetMask, Finset.mem_biUnion, allowedDeletions, deletionMask,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D,hD,hx⟩
    have he : (deletedVariables x).erase v ⊆ D := by
      intro w hw
      exact (Finset.mem_insert.mp (hx (Finset.mem_of_mem_erase hw))).resolve_left
        (Finset.ne_of_mem_erase hw)
    exact (Finset.card_le_card he).trans hD
  · intro hx
    refine ⟨(deletedVariables x).erase v,hx,?_⟩
    intro w hw
    by_cases he : w = v
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he,hw⟩))

theorem freeDeletionBudget_permutation {n r : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin n) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ freeDeletionBudgetMask n r (e v) ↔
      x ∈ freeDeletionBudgetMask n r v := by
  rw [mem_freeDeletionBudgetMask_erase, mem_freeDeletionBudgetMask_erase,
    deletedVariables_permutation, ← Finset.image_erase e.injective,
    Finset.card_image_of_injective _ e.injective]

theorem maskLifetime_permutation {n M : ℕ} (e : Equiv.Perm (Fin n))
    (U V : Finset (DeletionCandidate n)) (xs : Fin M → Finset (DeletionCandidate n))
    (hUV : ∀ x, candidatePermutation e x ∈ V ↔ x ∈ U) :
    maskLifetime M V (fun j => renameMask e (xs j)) = maskLifetime M U xs := by
  apply le_antisymm
  · apply maskLifetime_map_le (candidatePermutation e).symm
    · intro x hx
      have h := (hUV ((candidatePermutation e).symm x)).mp
      exact h (by simpa only [Equiv.apply_symm_apply] using hx)
    · intro j x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa only [Equiv.symm_apply_apply] using hy
  · apply maskLifetime_map_le (candidatePermutation e)
    · intro x hx
      exact (hUV x).mpr hx
    · intro j x hx
      exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem clauseMask_permutation_mem {n k : ℕ} (e : Equiv.Perm (Fin n))
    (cs : Fin k → SignedLiteral n) (x : DeletionCandidate n) :
    candidatePermutation e x ∈ clauseMask (fun j => literalPermutation e (cs j)) ↔
      x ∈ clauseMask cs := by
  simp only [clauseMask, Finset.mem_filter, Finset.mem_univ, true_and]
  change (¬∀ j, x (e.symm (e (cs j).1)) = some (!(cs j).2)) ↔
    (¬∀ j, x (cs j).1 = some (!(cs j).2))
  simp only [Equiv.symm_apply_apply]

def clausePermutation {n : ℕ} (e : Equiv.Perm (Fin n)) (k : ℕ) :
    Equiv.Perm (Fin k → SignedLiteral n) where
  toFun c j := literalPermutation e (c j)
  invFun c j := (literalPermutation e).symm (c j)
  left_inv c := by funext j; exact (literalPermutation e).symm_apply_apply _
  right_inv c := by funext j; exact (literalPermutation e).apply_symm_apply _

private theorem mem_clauseCounts {n k : ℕ} (x : DeletionCandidate n)
    (c : (Fin k → SignedLiteral n) → ℕ) :
    x ∈ countsMask clauseMask c ↔ ∀ a, c a = 0 ∨ x ∈ clauseMask a := by
  simp only [countsMask, Finset.mem_filter, Finset.mem_univ, true_and]

theorem countsMask_permutation {n k : ℕ} (e : Equiv.Perm (Fin n))
    (c : (Fin k → SignedLiteral n) → ℕ) :
    renameMask e (countsMask clauseMask c) =
      countsMask clauseMask (fun a => c ((clausePermutation e k).symm a)) := by
  ext x
  rw [renameMask, Finset.mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩
    apply (mem_clauseCounts _ _).mpr
    intro a
    rcases (mem_clauseCounts y c).mp hy ((clausePermutation e k).symm a) with hz | hm
    · exact Or.inl hz
    · right
      have he : (fun j => literalPermutation e (((clausePermutation e k).symm a) j)) = a :=
        (clausePermutation e k).apply_symm_apply a
      rw [← he]
      exact (clauseMask_permutation_mem e _ y).mpr hm
  · intro hx
    refine ⟨(candidatePermutation e).symm x, ?_, (candidatePermutation e).apply_symm_apply x⟩
    apply (mem_clauseCounts _ _).mpr
    intro a
    have h := (mem_clauseCounts x _).mp hx ((clausePermutation e k) a)
    simp only [Equiv.symm_apply_apply] at h
    rcases h with hz | hm
    · exact Or.inl hz
    · right
      have hmem := (clauseMask_permutation_mem e a ((candidatePermutation e).symm x)).mp
      apply hmem
      change x ∈ clauseMask (fun j => literalPermutation e (a j)) at hm
      simpa only [Equiv.apply_symm_apply] using hm

end

end FixedClauseThreshold.Computability

end OAI
