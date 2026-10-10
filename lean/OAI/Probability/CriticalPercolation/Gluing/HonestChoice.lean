import Mathlib

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical

namespace CriticalPercolation
variable {Ω I : Type*} [MeasurableSpace Ω]

def firstTest (P : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  if h : ∃ n, P n ω then Nat.find h else 0

omit [MeasurableSpace Ω] in
lemma firstTest_eq (P : ℕ → Ω → Prop) (ω : Ω) (n : ℕ) :
    firstTest P ω=n ↔ (P n ω ∧ ∀ m<n, ¬P m ω) ∨ ((¬∃ m, P m ω) ∧ n=0) := by
  by_cases h : ∃ m, P m ω
  · simp [firstTest,h,Nat.find_eq_iff]
  · have hn : ¬P n ω := fun hn => h ⟨n,hn⟩
    simp [firstTest,h,hn,eq_comm]

lemma measurableSet_firstTest (P : ℕ → Ω → Prop) (hP : ∀ n, MeasurableSet {ω | P n ω}) (n : ℕ) :
    MeasurableSet {ω | firstTest P ω=n} := by
  simp_rw [firstTest_eq]
  apply MeasurableSet.union
  · exact (hP n).inter ((Measurable.forall (fun m => measurable_const.imp (hP m).mem.not)).setOf)
  · exact (Measurable.exists (fun m => (hP m).mem)).setOf.compl.inter (MeasurableSet.const _)

theorem exists_honest_selector [Countable I] [Nonempty I] (P : Ω → I → Prop)
    (hP : ∀ i, MeasurableSet {ω | P ω i}) :
    ∃ d : Ω → I, (∀ i, MeasurableSet {ω | d ω=i}) ∧
      ∀ ω, (∃ i, P ω i) → P ω (d ω) := by
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let d : Ω → I := fun ω => e (firstTest (fun n ω => P ω (e n)) ω)
  refine ⟨d,?_,?_⟩
  · intro i
    have hh : {ω | d ω=i}=⋃ n : ℕ, ({ω | firstTest (fun n ω => P ω (e n)) ω=n}∩{_ω | e n=i}) := by
      ext ω
      simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨n,hn,hni⟩ => by dsimp [d]; rw [hn,hni]⟩
    rw [hh]
    exact MeasurableSet.iUnion (fun n => (measurableSet_firstTest _ (fun m => hP (e m)) n).inter
      (MeasurableSet.const _))
  · intro ω ⟨i,hi⟩
    obtain ⟨n,rfl⟩ := he i
    have hex : ∃ n, P ω (e n) := ⟨n,hi⟩
    dsimp [d,firstTest]
    rw [dite_eq_left hex]
    exact Nat.find_spec hex

end CriticalPercolation
end
end
end

end OAI
