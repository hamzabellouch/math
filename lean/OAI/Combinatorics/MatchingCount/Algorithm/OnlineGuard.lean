import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseCertificate
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineTrial

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource NumericMarking OnlineSchedule

def positive (q : Fraction) : Bool := TreeFraction.less ((0,1),q)
def positiveRealizer : TreeTyped.Realizer positive :=
  composition (pair (constant (0,1)) identity) lessRealizer
lemma polynomial_positive : PolynomialTime positiveRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant _) polynomial_identity) polynomial_less
lemma positive_repr {q : ℚ} (hq : 0≤q) : positive (repr q)=decide (0<q) := by
  rw [positive,less_val _ _ (by decide) q.pos,val_repr hq]
  simp [val]

def accept (x : SparseStageData×List SampleBits) : Bool :=
  x.2.any (fun b=>positive (sparseCertificate (x.1,b)))
def acceptRealizer : TreeTyped.Realizer accept :=
  (composition (mapWith (composition sparseCertificateRealizer positiveRealizer)) any).congr (by
    intro x; simp only [accept,Function.comp_def,List.any_map,Function.id_def])
lemma polynomial_accept : PolynomialTime acceptRealizer := by
  unfold acceptRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_mapWith (polynomial_composition polynomial_sparseCertificate polynomial_positive)) polynomial_any

def test (x : RequestInput) : Experiment Bool :=
  (OnlineSample.many (16,sourceRequest x)).map (fun bs=>accept (x.1,bs))
noncomputable def testRealizer : OnlineTree.Realizer test :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic first)
    (OnlineTree.composition (OnlineTree.deterministic (pair (constant 16) sourceRequestRealizer)) OnlineSample.manyRealizer))
    (OnlineTree.deterministic acceptRealizer)).congr (by
      intro x h; simp only [test,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

def finish (x : Fraction×Bool) : Fraction := if x.2 then x.1 else (0,1)
def finishRealizer : TreeTyped.Realizer finish :=
  (choose second first (constant (0,1))).congr (fun _=>rfl)
lemma polynomial_finish : PolynomialTime finishRealizer := by
  unfold finishRealizer; apply polynomial_congr; tree_cost

def checked (x : OnlineTrial.State) : Experiment Fraction :=
  (test x.1).map (fun b=>finish (x.2,b))
noncomputable def checkedRealizer : OnlineTree.Realizer checked :=
  (OnlineTree.composition (OnlineTree.pair (OnlineTree.deterministic second)
    (OnlineTree.composition (OnlineTree.deterministic first) testRealizer))
    (OnlineTree.deterministic finishRealizer)).congr (by
      intro x h; simp only [checked,Experiment.mean_bind,Experiment.mean_map,Experiment.mean])

def trial (x : List Bool×OnlineTrial.State) : Experiment Fraction :=
  (OnlineTrial.sweep x).bind checked
noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  OnlineTree.composition OnlineTrial.sweepRealizer checkedRealizer
end MatchingFPRAS.OnlineGuard

end OAI
