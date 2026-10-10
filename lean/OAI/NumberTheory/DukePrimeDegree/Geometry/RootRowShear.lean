import OAI.NumberTheory.DukePrimeDegree.Geometry.IteratedRootShear
import OAI.NumberTheory.DukePrimeDegree.Geometry.ExtremalRemainingEntries

namespace OAI

/-! # Conjugation by the next root is the product of its row shears -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

abbrev NextRoot (q : InitialRootStep n) := ↥(q.remaining.erase q.root)

def rowTargets (q : InitialRootStep n) : Finset q.NextRoot :=
  Finset.univ.filter (fun p => p.val.1 = q.root.1)

lemma row_source_mem (q : InitialRootStep n) (p : q.NextRoot) (hp : p.val.1 = q.root.1) :
    (q.root.2,p.val.2) ∈ q.remaining.erase q.root := by
  have hpR := (Finset.mem_erase.mp p.prop).2
  have hpne := (Finset.mem_erase.mp p.prop).1
  have hbc : q.root.2 < p.val.2 := by
    have hle : q.root.2 ≤ p.val.2 := by
      by_contra h
      exact not_lt_of_ge (q.least p.val hpR)
        (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hp,lt_of_not_ge h⟩))
    refine lt_of_le_of_ne hle ?_
    intro h
    exact hpne (Prod.ext hp h.symm)
  have hs : (q.root.2,p.val.2) ∈ allPositiveRoots n :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbc⟩
  refine Finset.mem_erase.mpr ⟨?_,Finset.mem_sdiff.mpr ⟨hs,?_⟩⟩
  · intro he
    exact q.distinct (congrArg Prod.fst he).symm
  · intro hP
    have hP' := (q.initial _ hP).2 p.val
      (Finset.mem_sdiff.mp hpR).1
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (hp ▸ q.positive)))
    exact (Finset.mem_sdiff.mp hpR).2 hP'

def rowSource (q : InitialRootStep n) (p : q.NextRoot) : q.NextRoot :=
  if hp : p.val.1 = q.root.1 then ⟨(q.root.2,p.val.2),q.row_source_mem p hp⟩ else p

lemma rowSource_val (q : InitialRootStep n) (p : q.NextRoot) (hp : p.val.1 = q.root.1) :
    (q.rowSource p).val = (q.root.2,p.val.2) := by simp [rowSource,hp]

lemma rowSource_not_target (q : InitialRootStep n) (p : q.NextRoot)
    (hp : p ∈ q.rowTargets) : q.rowSource p ∉ q.rowTargets := by
  have ha : p.val.1 = q.root.1 := (Finset.mem_filter.mp hp).2
  simp only [rowTargets,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [q.rowSource_val p ha]
  exact q.distinct.symm

def rowShear (q : InitialRootStep n) (r : ℝ) : (q.NextRoot → ℝ) → (q.NextRoot → ℝ) :=
  iteratedCoordinateShear q.rowSource r q.rowTargets.toList

lemma rowShear_apply (q : InitialRootStep n) (r : ℝ) (x : q.NextRoot → ℝ) (p : q.NextRoot) :
    q.rowShear r x p = if p.val.1 = q.root.1 then x p+r*x (q.rowSource p) else x p := by
  have h := iteratedCoordinateShear_apply q.rowSource r q.rowTargets.toList
    q.rowTargets.nodup_toList (by
      intro i hi
      simpa only [Finset.mem_toList] using q.rowSource_not_target i
        (Finset.mem_toList.mp hi)) x p
  simpa only [rowShear,Finset.mem_toList,rowTargets,Finset.mem_filter,
    Finset.mem_univ,true_and] using h

lemma rowShear_eq_conjugation_entries (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) (r : ℝ) (p : q.NextRoot) :
    q.rowShear (-r) (fun z => g.val.val z.val.1 z.val.2) p =
      ((Matrix.SpecialLinearGroup.transvection q.distinct (-r)) * g.val *
        Matrix.SpecialLinearGroup.transvection q.distinct r).val p.val.1 p.val.2 := by
  rw [q.rowShear_apply,q.conjugation_entry]
  by_cases hp : p.val.1 = q.root.1
  · have hpb : p.val.2 ≠ q.root.2 := by
      intro he
      exact (Finset.mem_erase.mp p.prop).1 (Prod.ext hp he)
    simp only [hp,ite_true,hpb,ite_false,q.rowSource_val p hp,sub_eq_add_neg]
    ring
  · simp [hp]

end InitialRootStep
end DukePrimeDegree

end

end OAI
