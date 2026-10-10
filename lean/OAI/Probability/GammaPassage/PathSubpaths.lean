import OAI.Probability.GammaPassage.GridVerticalPaths
import OAI.Probability.FirstPassage.Reversal

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

lemma pathIn_append_left (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn p ds S := by
  intro i hi
  have hh := h i (by simp only [List.length_append]; omega)
  simpa only [List.take_append,Nat.sub_eq_zero_of_le hi,List.take_zero,List.append_nil] using hh

lemma pathIn_append_right (p : Vertex) (ds es : List Step) (S : Set Vertex)
    (h : PathIn p (ds++es) S) : PathIn (p+displacement ds) es S := by
  intro i hi
  have hh := h (ds.length+i) (by simp only [List.length_append]; omega)
  simpa only [List.take_append,List.take_of_length_le (show ds.length ≤ ds.length+i by omega),
    Nat.add_sub_cancel_left,displacement_append,add_assoc] using hh

@[simp] lemma reverseSteps_append (ds es : List Step) :
    reverseSteps (ds++es)=reverseSteps es++reverseSteps ds := by simp [reverseSteps]

@[simp] lemma reverseSteps_reverse (ds : List Step) : reverseSteps (reverseSteps ds)=ds := by
  have hr (d : Step) : d.reverse.reverse=d := by cases d <;> rfl
  simp [reverseSteps,List.map_map,Function.comp_def,hr]

lemma pathIn_reverseSteps (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : PathIn (p+displacement ds) (reverseSteps ds) S := by
  induction ds generalizing p with
  | nil => simpa [reverseSteps] using h
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds S).mp h
    have hi := ih (p+d.delta) ht
    have hend : p+displacement (d::ds)+displacement (reverseSteps ds)=p+d.delta := by
      rw [displacement_cons,displacement_reverseSteps]
      abel
    have hs : PathIn (p+d.delta) [d.reverse] S := by
      apply (pathIn_cons_iff _ _ _ _).mpr
      refine ⟨?_,?_⟩
      · simpa using ht 0 (by omega)
      · intro i _
        simpa using hp
    have he : reverseSteps (d::ds)=reverseSteps ds++[d.reverse] := by simp [reverseSteps]
    rw [he]
    apply pathIn_append _ _ _ _ (by simpa [displacement_cons,add_assoc] using hi)
    simpa only [hend] using hs

/-- First visit to a column from its left, with the prefix staying to the left. -/
lemma path_first_column_up (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : p.1 ≤ X) (hend : X ≤ (p+displacement ds).1) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | z.1 ≤ X} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm hp (by simpa using hend),?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : (p+d.delta).1 ≤ X := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : X ≤ (p+d.delta+displacement ds).1 := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

/-- First visit to a column from its right, with the prefix staying to the right. -/
lemma path_first_column_down (p : Vertex) (ds : List Step) (X : ℤ)
    (hp : X ≤ p.1) (hend : (p+displacement ds).1 ≤ X) :
    ∃ pre rest : List Step, ds=pre++rest ∧ (p+displacement pre).1=X ∧
      PathIn p pre {z | X ≤ z.1} := by
  induction ds generalizing p with
  | nil =>
    refine ⟨[],[],rfl,by simpa using le_antisymm (by simpa using hend) hp,?_⟩
    intro i _
    simpa using hp
  | cons d ds ih =>
    by_cases he : p.1=X
    · refine ⟨[],d::ds,rfl,by simpa using he,?_⟩
      intro i _
      simpa using hp
    · have hp' : X ≤ (p+d.delta).1 := by
        cases d <;> simp only [Step.delta,Prod.fst_add] <;> omega
      have hend' : (p+d.delta+displacement ds).1 ≤ X := by
        simpa only [displacement_cons,add_assoc] using hend
      obtain ⟨pre,rest,heq,hcol,hin⟩ := ih (p+d.delta) hp' hend'
      refine ⟨d::pre,rest,by simp [heq],by simpa [displacement_cons,add_assoc] using hcol,?_⟩
      exact (pathIn_cons_iff ..).mpr ⟨hp,hin⟩

end GammaFPP.CrossingBridge

end OAI
