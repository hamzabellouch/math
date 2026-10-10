import Mathlib.Data.List.Pairwise
import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges
import OAI.NumberTheory.Ostmann.Construction.CompensationCellSeparation

namespace OAI

/-! # Finite tier labels for the actual disjoint compensation cells -/
namespace Ostmann
open scoped Classical

theorem selected_centers_pairwise_separated
    {A B : Set ℕ} {N hi : ℕ} {a C L X J : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {ws : List ℝ}
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs ws)
    (hw : ws.Pairwise (fun x y => y + J / 4 ≤ x))
    (hJ : 16 * (64 * tailDefectBudget a C X + 2) ≤ J) :
    cs.Pairwise (fun x y => y + 1 ≤ x) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  have hi : (i : ℕ) < ws.length := by rw [← hcs.length_eq]; exact i.isLt
  have hj : (j : ℕ) < ws.length := by rw [← hcs.length_eq]; exact j.isLt
  have hci := hcs.get i.isLt hi
  have hcj := hcs.get j.isLt hj
  have ht := hw.rel_get_of_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  have hs := compensation_cell_separation J (64 * tailDefectBudget a C X + 1)
    (ws.get ⟨i, hi⟩) (ws.get ⟨j, hj⟩) (cs.get i) (cs.get j)
    ht (by linarith) hci.1 (by simpa only [add_assoc] using hcj.2.1)
  exact_mod_cast hs

theorem selectedTailCellPrimes_disjoint_of_gap (A B : Set ℕ) (N hi : ℕ)
    (X : ℝ) (D : Finset ℕ) (i j : ℕ) (h : j + 1 ≤ i) :
    Disjoint (selectedTailCellPrimes A B N X hi D i)
      (selectedTailCellPrimes A B N X hi D j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hi := mem_primeLogCellSet_iff.mp
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  have hj := mem_primeLogCellSet_iff.mp
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hq).1).1
  have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
  linarith [hi.2.2.1, hj.2.2.2]

theorem selected_cells_pairwiseDisjoint (A B : Set ℕ) (N hi : ℕ)
    (X : ℝ) (D : Finset ℕ) (cs : List ℕ)
    (h : cs.Pairwise (fun x y => y + 1 ≤ x)) :
    Pairwise (fun i j : Fin cs.length =>
      Disjoint (selectedTailCellPrimes A B N X hi D (cs.get i))
        (selectedTailCellPrimes A B N X hi D (cs.get j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _ (h.rel_get_of_lt hij)
  · exact (selectedTailCellPrimes_disjoint_of_gap A B N hi X D _ _
      (h.rel_get_of_lt hij)).symm

noncomputable def finitePrimeCellTier {k : ℕ} (Q : Fin k → Finset ℕ)
    (fallback : ℕ) (p : ℕ) : ℕ :=
  if h : ∃ i, p ∈ Q i then (Classical.choose h : Fin k) else fallback

theorem finitePrimeCellTier_of_mem {k : ℕ} (Q : Fin k → Finset ℕ)
    (hQ : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (fallback : ℕ) (i : Fin k) (p : ℕ) (hp : p ∈ Q i) :
    finitePrimeCellTier Q fallback p = i := by
  have hex : ∃ i, p ∈ Q i := ⟨i, hp⟩
  rw [finitePrimeCellTier, dite_eq_left hex]
  have he : Classical.choose hex = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hQ hne)) (Classical.choose_spec hex) hp
  exact congrArg Fin.val he

theorem finitePrimeCellTier_outside {k : ℕ} (Q : Fin k → Finset ℕ)
    (fallback p : ℕ) (hp : ∀ i, p ∉ Q i) :
    finitePrimeCellTier Q fallback p = fallback := by
  rw [finitePrimeCellTier, dite_eq_right]
  rintro ⟨i, hi⟩
  exact hp i hi

theorem selected_top_compensation_gap
    {A B : Set ℕ} {N hi top j : ℕ} {a C L X J cb w : ℝ} {D : Finset ℕ}
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hj : SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
    (hcb : 0 ≤ cb) (hw : 3 * J / 4 ≤ w)
    (hJ : 48 * (64 * tailDefectBudget a C X + 2) ≤ J) : top + 1 ≤ j := by
  have ht := htop.2.1
  have hc := hj.1
  have he : (top : ℝ) + 1 ≤ j := by linarith
  exact_mod_cast he

theorem finitePrimeCellTier_rest {k : ℕ} (Q : Fin k → Finset ℕ) (R : Finset ℕ)
    (hR : ∀ i, Disjoint R (Q i)) (p : ℕ) (hp : p ∈ R) :
    finitePrimeCellTier Q k p = k := by
  apply finitePrimeCellTier_outside
  intro i hpi
  exact (Finset.disjoint_left.mp (hR i)) hp hpi

theorem exists_selected_prime_tiers (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D R : Finset ℕ) (cs : List ℕ)
    (hcs : cs.Pairwise (fun x y => y + 1 ≤ x))
    (hR : ∀ i : Fin cs.length,
      Disjoint R (selectedTailCellPrimes A B N X hi D (cs.get i))) :
    ∃ tier : ℕ → ℕ,
      (∀ i : Fin cs.length, ∀ p ∈ selectedTailCellPrimes A B N X hi D (cs.get i),
        tier p = i) ∧ (∀ p ∈ R, tier p = cs.length) := by
  let Q := fun i : Fin cs.length => selectedTailCellPrimes A B N X hi D (cs.get i)
  refine ⟨finitePrimeCellTier Q cs.length, ?_, ?_⟩
  · exact finitePrimeCellTier_of_mem Q (selected_cells_pairwiseDisjoint A B N hi X D cs hcs)
      cs.length
  · exact finitePrimeCellTier_rest Q R hR

theorem mem_drop_index {A : Type} (cs : List A) (n : ℕ) (c : A) (hc : c ∈ cs.drop n) :
    ∃ i : Fin cs.length, n ≤ i ∧ cs.get i = c := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
  have hij : n + j.val < cs.length := by
    have h := j.isLt
    simp only [List.length_drop] at h
    omega
  refine ⟨⟨n + j.val, hij⟩, by simp, ?_⟩
  simpa only [List.get_eq_getElem, List.getElem_drop, Nat.add_comm] using hj

theorem exists_scheduled_prime_tiers (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D Qb : Finset ℕ) (top : ℕ) (cs : List ℕ) (tier : ℕ → ℕ)
    (hcomp : ∀ i : Fin cs.length,
      ∀ p ∈ selectedTailCellPrimes A B N X hi D (cs.get i), tier p = i)
    (htop : ∀ p ∈ selectedTailCellPrimes A B N X hi D top, tier p = cs.length)
    (hbulk : ∀ p ∈ Qb, tier p = cs.length) (n m offset : ℕ) (hoffset : offset ≤ cs.length) :
    ∃ tierB : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m → ℕ,
      (∀ i, offset ≤ tierB i) ∧
      (∀ i p, p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
        Qb top (cs.drop offset) n m i → tier p = tierB i) := by
  have hex (i : MovingRegularSlot n (scheduledSmallLength (cs.drop offset)) m) :
      ∃ b, offset ≤ b ∧ ∀ p,
        p ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
          Qb top (cs.drop offset) n m i → tier p = b := by
    rcases i with ⟨u, i | i⟩
    · have hs : scheduledSmallCell top (cs.drop offset) i = top ∨
          scheduledSmallCell top (cs.drop offset) i ∈ cs.drop offset :=
        scheduledSmallCell_property (fun c => c = top ∨ c ∈ cs.drop offset) top
          (cs.drop offset) (Or.inl rfl) (fun c hc => Or.inr hc) i
      rcases hs with hs | hs
      · refine ⟨cs.length, hoffset, ?_⟩
        intro p hp
        change p ∈ selectedTailCellPrimes A B N X hi D
          (scheduledSmallCell top (cs.drop offset) i) at hp
        exact htop p (hs ▸ hp)
      · obtain ⟨j, hj, he⟩ := mem_drop_index cs offset _ hs
        refine ⟨j.val, hj, ?_⟩
        intro p hp
        apply hcomp j p
        change p ∈ selectedTailCellPrimes A B N X hi D
          (scheduledSmallCell top (cs.drop offset) i) at hp
        rwa [he]
    · exact ⟨cs.length, hoffset, hbulk⟩
  choose b hb ht using hex
  exact ⟨b, hb, ht⟩

end Ostmann

end OAI
