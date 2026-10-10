import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSuccess
import OAI.Analysis.HardSphere.Geometry.LocalCheck

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma jointCollision_closed {L : Length} (r : ℝ) :
    IsClosed {p : C(Time,Point)×C(Time,Point) | TrialCollision r (projectCurve L p.2) p.1} := by
  let E : Set ((C(Time,Point)×C(Time,Point))×Time) :=
    {p | torusDistance L (projectPoint L (p.1.1 p.2)) (projectPoint L (p.1.2 p.2))≤r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f:=fun p : (C(Time,Point)×C(Time,Point))×Time ↦
      (projectPoint L (p.1.1 p.2),projectPoint L (p.1.2 p.2)))
    unfold projectPoint
    fun_prop
  convert isClosedMap_fst_of_compactSpace E hE using 1
  ext p
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(p,s),hs,rfl⟩,fun ⟨⟨q,s⟩,hs,hq⟩ ↦ by
    change q=p at hq
    subst q
    exact ⟨s,hs⟩⟩

variable {I : Type*} [DecidableEq I] {L : Length}
  (S : I→Set C(Time,Point))

def physicalPairCheck (r : ℝ) (i j : I) (hij : i≠j) : LocalCheck (fun i ↦ S i) where
  support := {i,j}
  nonempty := ⟨i,by simp⟩
  arity := (Finset.card_pair hij).le
  pass x := ¬TrialCollision r (projectCurve L (x j).val) (x i).val
  measurable_pass := by
    have hm : Measurable (fun x : ∀i,S i ↦ ((x i).val,(x j).val)) := by fun_prop
    exact ((jointCollision_closed (L:=L) r).measurableSet.preimage hm).compl
  depends x y h := by
    rw [h i (by simp),h j (by simp)]

lemma physicalPairCheck_symmetric (r : ℝ) (f g : C(Time,Point)) :
    TrialCollision (L:=L) r (projectCurve L g) f ↔ TrialCollision r (projectCurve L f) g := by
  unfold TrialCollision
  apply exists_congr
  intro s
  change torusDistance L (projectPoint L (f s)) (projectPoint L (g s))≤r ↔
    torusDistance L (projectPoint L (g s)) (projectPoint L (f s))≤r
  rw [torusDistance_comm]

end HardSphere.Bridge

end
end

end

end OAI
