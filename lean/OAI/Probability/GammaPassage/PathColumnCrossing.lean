import OAI.Probability.GammaPassage.PathSubpaths

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

/-- Last-left/first-right subcrossing from an actual finite path. The middle
path stays between the two columns; both outside pieces are retained. -/
theorem path_column_subcrossing (p : Vertex) (ds : List Step) (A B : ℤ)
    (hp : p.1 ≤ A) (hAB : A ≤ B) (hend : B ≤ (p+displacement ds).1) :
    ∃ pre mid post : List Step, ds=pre++mid++post ∧
      (p+displacement pre).1=A ∧
      (p+displacement pre+displacement mid).1=B ∧
      PathIn (p+displacement pre) mid {z | A ≤ z.1 ∧ z.1 ≤ B} := by
  obtain ⟨front,post,he,hB,hinB⟩ := path_first_column_up p ds B (hp.trans hAB) hend
  let zB := p+displacement front
  have hrev : zB+displacement (reverseSteps front)=p := by simp [zB]
  obtain ⟨revMid,revPre,heR,hA,hinA⟩ := path_first_column_down zB (reverseSteps front) A
    (by change A ≤ (p+displacement front).1; omega) (by rw [hrev]; exact hp)
  have hfront : front=reverseSteps revPre++reverseSteps revMid := by
    have hh := congrArg reverseSteps heR
    simpa only [reverseSteps_reverse,reverseSteps_append] using hh
  have hfull : zB+displacement revMid+displacement revPre=p := by
    rw [heR,displacement_append,← add_assoc] at hrev
    exact hrev
  have hstart : p+displacement (reverseSteps revPre)=zB+displacement revMid := by
    rw [displacement_reverseSteps,← hfull]
    abel
  have hmid : p+displacement (reverseSteps revPre)+displacement (reverseSteps revMid)=zB := by
    rw [hstart,displacement_reverseSteps]
    abel
  refine ⟨reverseSteps revPre,reverseSteps revMid,post,by rw [he,hfront],?_,?_,?_⟩
  · rw [hstart]
    exact hA
  · rw [hmid]
    exact hB
  · have hl := pathIn_reverseSteps zB revMid {z | A ≤ z.1} hinA
    have hu := pathIn_append_right p (reverseSteps revPre) (reverseSteps revMid) {z | z.1 ≤ B}
      (by rw [← hfront]; exact hinB)
    rw [← hstart] at hl
    intro i hi
    exact ⟨hl i hi,hu i hi⟩

/-- Any middle part of a path inherits the original vertex localization. -/
lemma pathIn_middle (p : Vertex) (pre mid post : List Step) (S : Set Vertex)
    (h : PathIn p (pre++mid++post) S) : PathIn (p+displacement pre) mid S :=
  pathIn_append_right p pre mid S (pathIn_append_left p (pre++mid) post S h)

end GammaFPP.CrossingBridge

end OAI
