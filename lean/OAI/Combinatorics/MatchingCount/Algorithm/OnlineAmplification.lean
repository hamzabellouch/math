import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineGuardLaw
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineMedian

namespace OAI

namespace MatchingFPRAS.OnlineAmplification
open PhysicalStream TreeTyped

abbrev TrialInput := List Bool×OnlineTrial.State

def trials (x : ℕ×TrialInput) : Experiment (List TreeFraction.Fraction) :=
  OnlineTree.traverseM OnlineGuard.trial (List.replicate x.1 x.2)
noncomputable def trialsRealizer : OnlineTree.Realizer trials :=
  OnlineTree.composition (OnlineTree.deterministic OnlineSample.repeatInputRealizer)
    (OnlineTree.traverse OnlineGuard.trialRealizer)
def run (x : ℕ×TrialInput) : Experiment TreeFraction.Fraction := (trials x).map OnlineMedian.median
noncomputable def runRealizer : OnlineTree.Realizer run :=
  (OnlineTree.composition trialsRealizer (OnlineTree.deterministic OnlineMedian.medianRealizer)).congr (by
    intro x h; simp only [run,Experiment.mean_map,Experiment.mean_bind,Experiment.mean])

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def initial (p : Trial.Parameters G) : TrialInput :=
  (List.replicate p.K false,OnlineTrial.represent p (FiniteTrial.firstLayer p) PUnit.unit)
lemma trials_mean (p : Trial.Parameters G) (r : ℕ) (h : List TreeFraction.Fraction→ℚ) :
    (trials (r,initial p)).mean h=qaverage (fun bs : Fin r→(Fin (FiniteTrial.guardedBits p)→Bool)=>
      h (List.ofFn (fun i=>TreeFraction.repr (FiniteTrial.guardedBitOutput p (bs i))))) := by
  rw [trials,←List.ofFn_const]
  exact mean_traverse_ofFn OnlineGuard.trial r (fun _=>initial p)
    (fun _ b=>TreeFraction.repr (FiniteTrial.guardedBitOutput p b)) (fun _=>OnlineGuard.trial_mean p) h
lemma run_mean (p : Trial.Parameters G) (δ : ℚ) (h : TreeFraction.Fraction→ℚ) :
    (run (2*Amplification.halfRepetitions δ+1,initial p)).mean h=
      qaverage (fun b=>h (TreeFraction.repr (FiniteTrial.guardedAmplifiedBitOutput p δ b))) := by
  rw [run,Experiment.mean_map,trials_mean]
  simp_rw [OnlineMedian.median_repr _ (fun _=>FiniteTrial.guardedBitOutput_nonneg p _)]
  change _=qaverage ((fun bs : Fin (2*Amplification.halfRepetitions δ+1)→(Fin (FiniteTrial.guardedBits p)→Bool)=>
    h (TreeFraction.repr (Amplification.median (fun i=>FiniteTrial.guardedBitOutput p (bs i))))) ∘
      Transport.matrixBitsEquiv (2*Amplification.halfRepetitions δ+1) (FiniteTrial.guardedBits p))
  exact (qaverage_equiv _ _).symm
end MatchingFPRAS.OnlineAmplification

end OAI
