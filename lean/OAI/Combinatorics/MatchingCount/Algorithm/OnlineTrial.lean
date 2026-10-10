import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineRequest

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule

abbrev State := RequestInput×Fraction

def advance (x : SparseStageData×Vector) : SparseStageData :=
  (((x.1.1.1.1,false::x.1.1.1.2),x.1.1.2),x.2)
def advanceRealizer : TreeTyped.Realizer advance :=
  (TreeTyped.pair (TreeTyped.pair
    (TreeTyped.pair first.fst.fst.fst (composition (TreeTyped.pair (constant false) first.fst.fst.snd) listCons))
    first.fst.snd) second).congr (fun _=>rfl)
lemma polynomial_advance : PolynomialTime advanceRealizer := by
  unfold advanceRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  tree_cost

def carry (x : State×(Fraction×Vector)) : State :=
  ((advance (x.1.1.1,x.2.2),x.1.1.2),TreeFraction.mul (x.1.2,x.2.1))
def carryRealizer : TreeTyped.Realizer carry :=
  (TreeTyped.pair (TreeTyped.pair
    (composition (TreeTyped.pair first.fst.fst second.snd) advanceRealizer) first.fst.snd)
    (composition (TreeTyped.pair first.snd second.fst) mulRealizer)).congr (fun _=>rfl)
lemma polynomial_carry : PolynomialTime carryRealizer := by
  unfold carryRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_advance
  have := polynomial_mul
  tree_cost

def prepare (x : RequestInput) : OnlineStage.Input :=
  (x.1,(x.2,sourceRequest x))
def prepareRealizer : TreeTyped.Realizer prepare :=
  TreeTyped.pair first (TreeTyped.pair second sourceRequestRealizer)
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  TreeTyped.polynomial_pair polynomial_first (TreeTyped.polynomial_pair polynomial_second polynomial_sourceRequest)

def step (x : State) : Experiment State :=
  (OnlineStage.execute (prepare x.1)).map (fun y=>carry (x,y))
noncomputable def stepRealizer : OnlineTree.Realizer step :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic TreeTyped.identity)
    (OnlineTree.composition (OnlineTree.deterministic (composition first prepareRealizer)) OnlineStage.executeRealizer))
    (OnlineTree.deterministic carryRealizer)).congr (by
      intro x h
      simp only [step,Experiment.mean_bind,Experiment.mean_map,Experiment.mean,Function.comp_apply,id_eq])

def body (x : Bool×State) : Experiment State := step x.2
noncomputable def bodyRealizer : OnlineTree.Realizer body :=
  (OnlineTree.composition (OnlineTree.deterministic TreeTyped.second) stepRealizer).congr (by
    intro x h; rfl)

def sweep (x : List Bool×State) : Experiment State := OnlineTree.foldM body x.1 x.2
noncomputable def sweepRealizer : OnlineTree.Realizer sweep := OnlineTree.fold bodyRealizer
end MatchingFPRAS.OnlineTrial

end OAI
