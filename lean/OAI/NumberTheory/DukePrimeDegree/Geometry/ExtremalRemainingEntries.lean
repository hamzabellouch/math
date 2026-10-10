import OAI.NumberTheory.DukePrimeDegree.Geometry.ExtremalConjugationEntries
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootHolonomy

namespace OAI

/-! # Exact entries of extremal-root conjugation on the remaining group -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma first_le (q : InitialRootStep n) (p : Fin n × Fin n) (hp : p ∈ q.remaining) :
    q.root.1 ≤ p.1 := by
  by_contra h
  exact not_lt_of_ge (q.least p hp)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (lt_of_not_ge h)))

lemma remaining_standard_column (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup q.remaining) (i : Fin n) :
    g.val.val i q.root.1 = if i = q.root.1 then 1 else 0 := by
  have hnot : (i,q.root.1) ∉ q.remaining := by
    intro h
    exact not_lt_of_ge (q.first_le _ h) (q.remaining_positive _ h)
  exact positiveRootGeneratedGroup_pattern q.remaining q.remaining_closed g.prop i q.root.1 hnot

lemma next_selected_entry (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    g.val.val q.root.1 q.root.2 = 0 := by
  have hg : g.val ∈ positiveRootGeneratedGroup q.remaining :=
    positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) g.prop
  have hpat := positiveRootGeneratedGroup_pattern (q.remaining.erase q.root)
    (by
      intro a b c hab hbc
      refine Finset.mem_erase.mpr ⟨?_,q.remaining_closed a b c
        (Finset.mem_erase.mp hab).2 (Finset.mem_erase.mp hbc).2⟩
      intro he
      have ha := q.remaining_positive (a,b) (Finset.mem_erase.mp hab).2
      have hb := q.remaining_positive (b,c) (Finset.mem_erase.mp hbc).2
      have hleast := q.least (a,b) (Finset.mem_erase.mp hab).2
      have hae : a = q.root.1 := congrArg Prod.fst he
      have hce : c = q.root.2 := congrArg Prod.snd he
      exact not_lt_of_ge hleast (Prod.Lex.toLex_lt_toLex.mpr
        (Or.inr ⟨hae,hce ▸ hb⟩))) g.prop
  simpa [Matrix.one_apply,q.distinct] using hpat q.root.1 q.root.2 (Finset.notMem_erase _ _)

lemma conjugation_entry (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root))
    (r : ℝ) (i j : Fin n) :
    ((Matrix.SpecialLinearGroup.transvection q.distinct (-r)) * g.val *
      Matrix.SpecialLinearGroup.transvection q.distinct r).val i j =
      if i = q.root.1 then
        if j = q.root.2 then 0 else g.val.val q.root.1 j - r * g.val.val q.root.2 j
      else g.val.val i j := by
  let w : positiveRootGeneratedGroup q.remaining :=
    ⟨g.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) g.prop⟩
  have hbb : g.val.val q.root.2 q.root.2 = 1 :=
    upperRoot_diagonal (positiveRootGeneratedGroup_mono
      (Finset.sdiff_subset : q.remaining ⊆ allPositiveRoots n) w.prop) _
  rw [conjugation_entry_of_standard_column q.distinct g.val
    (q.remaining_standard_column w) hbb,q.next_selected_entry g]

end InitialRootStep
end DukePrimeDegree

end

end OAI
