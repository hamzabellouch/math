import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineLadderSchedule
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineSampleCount
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineAmplification

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule

abbrev Seed := GraphData×(Fraction×Fraction)
abbrev Config := (Seed×ℕ)×(ℕ×ℕ)

def seedK (x : Seed) : Seed×ℕ := (x,coolingSchedule (x.1.1.length,x.2.1))
def seedKRealizer : Realizer seedK :=
  (pair identity (composition (g:=coolingSchedule) (pair (composition first.fst listLength) second.fst) coolingScheduleRealizer)).congr (fun _=>rfl)
def seedN (x : Seed×ℕ) : (Seed×ℕ)×ℕ := (x,vertexNumber (x.1.1.1.length,x.2))
def seedNRealizer : Realizer seedN :=
  (pair identity (composition (g:=vertexNumber) (pair (composition first.fst.fst listLength) second) vertexNumberRealizer)).congr (fun _=>rfl)
def seedD (x : (Seed×ℕ)×ℕ) : Config :=
  (x.1,(x.2,distortion (x.1.1.1.1.length,x.2)))
def seedDRealizer : Realizer seedD :=
  pair first (pair second (composition (pair (composition first.fst.fst.fst listLength) second) distortionRealizer))
def config (x : Seed) : Config := seedD (seedN (seedK x))
def configRealizer : Realizer config := composition (composition seedKRealizer seedNRealizer) seedDRealizer

def root (n : ℕ) : ℕ := findRoot (n-1,List.replicate n false)
def rootRealizer : Realizer root :=
  composition (pair (composition (pair identity (constant 1)) subtract) (composition identity fuelRealizer)) findRootRealizer
lemma root_eq (n : ℕ) : root n=(n-1).sqrt := by
  apply findRoot_eq
  simpa using (Nat.sqrt_le_self (n-1)).trans (Nat.sub_le n 1)
def initialScale (n : ℕ) : Fraction := TreeFraction.div ((1,1),(root n,1))
def initialScaleRealizer : Realizer initialScale :=
  composition (pair (constant (1,1)) (pair rootRealizer (constant 1))) divRealizer
lemma initialScale_repr (n : ℕ) : initialScale n=TreeFraction.repr (Initializer.initialScale n) := by
  unfold initialScale
  rw [root_eq,←repr_nat ((n-1).sqrt),show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,div_repr (by decide) (by positivity)]
  rfl

def scaleVector (vs : List ℕ) : Vector := vs.map (fun i=>(i,initialScale vs.length))
def scaleVectorRealizer : Realizer scaleVector :=
  (composition (pair (composition listLength initialScaleRealizer) identity)
    (mapWith (pair second first))).congr (fun _=>rfl)
lemma scaleVector_source (G : GraphInput) (hn : 2≤G.n) :
    scaleVector (List.range G.n)=vectorRep (FiniteTrial.initialScaleState G hn).scale := by
  unfold scaleVector vectorRep
  rw [List.length_range,initialScale_repr]
  apply List.ext_getElem
  · simp
  · intro _ _ _
    simp [FiniteTrial.initialScaleState]

def nRealizer : Realizer (fun x : Config=>x.1.1.1.1.length) := composition first.fst.fst.fst listLength

def count (x : Config) : ℕ := sampleCount (x.1.1.1.1.length,((x.2.2,x.1.2),x.1.1.2.1))
def countRealizer : Realizer count :=
  composition (pair nRealizer (pair (pair second.snd first.snd) first.fst.snd.fst)) sampleCountRealizer

def data (x : Config) : SparseStageData :=
  (((x.1.1.1,[]),(((List.replicate (2*x.1.2+2) false,List.replicate (2*x.1.2) false),x.2.2),
    (List.replicate (ladderSchedule (x.2,x.1.2)) false,List.replicate (Transport.ladderQ x.2.1 x.2.2) false))),
    scaleVector x.1.1.1.1)
def dataRealizer : Realizer data :=
  (pair (pair (pair first.fst.fst (constant []))
    (pair (pair (pair (composition (g:=fun n=>List.replicate n false) (((constant 2).mulNat first.snd).addNat (constant 2)) fuelRealizer)
      (composition ((constant 2).mulNat first.snd) fuelRealizer)) second.snd)
      (pair (composition (composition (pair second first.snd) ladderScheduleRealizer) fuelRealizer)
        (composition (composition second qRealizer) fuelRealizer))))
    (composition first.fst.fst.fst scaleVectorRealizer)).congr (fun _=>rfl)

def trialInput (x : Config) : OnlineAmplification.TrialInput :=
  (List.replicate x.1.2 false,((data x,count x),(UnitRefresh.pairingCount x.1.1.1.1.length,1)))
def trialInputRealizer : Realizer trialInput :=
  pair (composition first.snd fuelRealizer)
    (pair (pair dataRealizer countRealizer) (pair (composition nRealizer pairingNumber) (constant 1)))
def runInput (x : Config) : ℕ×OnlineAmplification.TrialInput :=
  (repetitions x.1.1.2.2,trialInput x)
def runInputRealizer : Realizer runInput :=
  (pair (composition (g:=repetitions) first.fst.snd.snd repetitionsRealizer) trialInputRealizer).congr (fun _=>rfl)

def initializeInput (x : Seed) : ℕ×OnlineAmplification.TrialInput := runInput (config x)
def initializeInputRealizer : Realizer initializeInput := composition configRealizer runInputRealizer
end MatchingFPRAS.OnlineInitial

end OAI
