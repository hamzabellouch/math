import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineInitial

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule
open Transport Enlargement

variable {G : GraphInput} [Nontrivial (Fin G.n)]
variable (hn : 2≤G.n) (heven : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1)
local notation "p" => FiniteTrial.parameters G hn heven ε he he1
noncomputable def sourceSeed : Seed := (graphRep G,(TreeFraction.repr ε,TreeFraction.repr δ))
lemma config_source : config (sourceSeed (G:=G) ε δ)=
    ((sourceSeed (G:=G) ε δ,(p).K),((p).N,FiniteTrial.sourceD (G:=G) (p).K)) := by
  have hl : (graphRep G).1.length=G.n := by simp [graphRep]
  unfold config seedK seedN seedD sourceSeed
  dsimp only
  rw [hl,coolingSchedule_eq G.n hn ε he he1]
  change ((_,(p).K),(vertexNumber (G.n,(p).K),distortion (G.n,vertexNumber (G.n,(p).K))))=_
  rw [distortion_source,vertexNumber_eq]
  rfl
lemma data_source : data (config (sourceSeed (G:=G) ε δ))=
    OnlineStage.fixedData p (FiniteTrial.initialScaleState G hn) := by
  rw [config_source hn heven ε δ he he1]
  unfold data sourceSeed OnlineStage.fixedData OnlineStage.data
  dsimp only
  rw [show (graphRep G).1=List.range G.n from rfl,scaleVector_source G hn,ladderSchedule_eq _ _ _ (p).N_pos]
  rfl
lemma count_source : count (config (sourceSeed (G:=G) ε δ))=(p).S := by
  rw [config_source hn heven ε δ he he1]
  unfold count sourceSeed
  dsimp only
  have hl : (graphRep G).1.length=G.n := by simp [graphRep]
  rw [hl]
  exact sampleCount_source p
lemma trialInput_source : trialInput (config (sourceSeed (G:=G) ε δ))=OnlineAmplification.initial p := by
  unfold trialInput
  rw [data_source hn heven ε δ he he1,count_source hn heven ε δ he he1,config_source hn heven ε δ he he1]
  unfold OnlineAmplification.initial OnlineTrial.represent OnlineTrial.product
  simp only [FiniteTrial.firstLayer,Fin.prod_univ_zero,mul_one]
  have hg : (sourceSeed (G:=G) ε δ).1.1.length=G.n := by simp [sourceSeed,graphRep]
  rw [hg,GraphBridge.complete_count]
  rw [TreeFraction.repr_nat]
lemma initializeInput_source (hd : 0≤δ) : initializeInput (sourceSeed (G:=G) ε δ)=
    (2*Amplification.halfRepetitions δ+1,OnlineAmplification.initial p) := by
  unfold initializeInput runInput
  rw [trialInput_source hn heven ε δ he he1,config_source hn heven ε δ he he1]
  dsimp only [sourceSeed]
  rw [repetitions_repr δ hd]
end MatchingFPRAS.OnlineInitial

end OAI
