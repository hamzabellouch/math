import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorWordProgram
import OAI.Combinatorics.ContingencyTables.Counting.EstimatorWordBanks

namespace OAI

/-! # The executed estimator consumes exactly its independent sample banks -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS RootedEstimatorLayoutProgram
open DensePrograms GridBoundary
open scoped Classical

abbrev Banks (c : Context) := EstimatorWordBanks.Banks c.2.1.1 c.2.1.2
  (ratioWidth c) (correctionWalkWidth c) (binWidth c)

def wordEquiv (c : Context) : (Fin (wordWidth c) → Bool) ≃ Banks c :=
  EstimatorWordBanks.wordEquiv c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c)

def input (c : Context) (markers : List Bool×List Bool)
    (bits : Fin (wordWidth c) → Bool) : Input := (c,(markers,List.ofFn bits))

def encodeBanks (state : State) (j h count : ℕ) (markers : List Bool×List Bool)
    {S r t b : ℕ} (banks : EstimatorWordBanks.Banks j S r t b) :
    RootedEstimatorBlockProgram.Input :=
  ((count,List.ofFn (fun a => List.ofFn (fun i =>
      (phase (state,a.val),List.ofFn (banks.1 a i))))),
    List.ofFn (fun i => ((phase (state,j),h),
      (markers,(List.ofFn (banks.2 i).1,List.ofFn (banks.2 i).2)))))

def recodeBanks {j S r t b r' t' b' : ℕ} (hr : r=r') (ht : t=t') (hb : b=b') :
    EstimatorWordBanks.Banks j S r t b ≃ EstimatorWordBanks.Banks j S r' t' b' :=
  Equiv.cast (by rw [hr,ht,hb])

lemma encodeBanks_recode {j S r t b r' t' b' : ℕ} (hr : r=r') (ht : t=t') (hb : b=b')
    (state : State) (h count : ℕ) (markers : List Bool×List Bool)
    (banks : EstimatorWordBanks.Banks j S r t b) :
    encodeBanks state j h count markers (recodeBanks hr ht hb banks)=
      encodeBanks state j h count markers banks := by
  cases hr
  cases ht
  cases hb
  rfl

def bankInput (c : Context) (markers : List Bool×List Bool) (banks : Banks c) :
    RootedEstimatorBlockProgram.Input :=
  encodeBanks c.1 c.2.1.1 c.2.2.2 (assignmentCount c) markers banks

private lemma ratioBlock_input (c : Context) (markers : List Bool×List Bool)
    (hr : 0 < ratioWidth c) (bits : Fin (wordWidth c) → Bool) (a : Fin c.2.1.1) :
    ratioBlock (input c markers bits,a.val)=List.ofFn (fun i =>
      (phase (c.1,a.val),List.ofFn ((wordEquiv c bits).1 a i))) := by
  change (DensePrograms.wordChunks (ratioWidth c,
    DensePrograms.wordChunk ((c.2.1.2*ratioWidth c,
      (List.ofFn bits).take (c.2.1.1*(c.2.1.2*ratioWidth c))),a.val))).map
        (fun bs => (phase (c.1,a.val),bs))=_
  have hc := EstimatorWordBanks.ratio_chunks c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) hr bits a
  have hm := congrArg (List.map (fun bs => (phase (c.1,a.val),bs))) hc
  refine hm.trans ?_
  rw [List.map_ofFn]
  rfl

private lemma ratioBlocks_input (c : Context) (markers : List Bool×List Bool)
    (hs : 0 < c.2.1.2) (hr : 0 < ratioWidth c) (bits : Fin (wordWidth c) → Bool) :
    ratioBlocks (input c markers bits)=List.ofFn (fun a => List.ofFn (fun i =>
      (phase (c.1,a.val),List.ofFn ((wordEquiv c bits).1 a i)))) := by
  have hrows : ratioRows (input c markers bits)=List.range c.2.1.1 :=
    EstimatorWordBanks.ratio_rows _ _ _ _ _ hs hr bits
  unfold ratioBlocks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hi' : i < c.2.1.1 := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact ratioBlock_input c markers hr bits ⟨i,hi'⟩

private lemma correctionBlock_input (c : Context) (markers : List Bool×List Bool)
    (ht : 0 < correctionWidth c) (bits : Fin (wordWidth c) → Bool) :
    correctionBlock (input c markers bits)=List.ofFn (fun i =>
      ((phase (c.1,c.2.1.1),c.2.2.2),
        (markers,(List.ofFn ((wordEquiv c bits).2 i).1,List.ofFn ((wordEquiv c bits).2 i).2)))) := by
  have hw : correctionWords (input c markers bits)=List.ofFn (fun i : Fin c.2.1.2 =>
      List.ofFn (gridWordEquiv c.2.1.2 (correctionWalkWidth c+binWidth c)
        (FairBits.splitWordEquiv (c.2.1.1*(c.2.1.2*ratioWidth c))
          (c.2.1.2*(correctionWalkWidth c+binWidth c)) bits).2 i)) :=
    EstimatorWordBanks.correction_chunks _ _ _ _ _ ht bits
  rw [correctionBlock,hw,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change ((phase (c.1,c.2.1.1),c.2.2.2),
    (markers,((List.ofFn _).take (correctionWalkWidth c),
      (List.ofFn _).drop (correctionWalkWidth c))))=_
  have htake := EstimatorWordBanks.correction_take c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) bits i
  have hdrop := EstimatorWordBanks.correction_drop c.2.1.1 c.2.1.2
    (ratioWidth c) (correctionWalkWidth c) (binWidth c) bits i
  exact congrArg (fun ws : List Bool × List Bool =>
    ((phase (c.1,c.2.1.1),c.2.2.2),(markers,ws))) (Prod.ext htake hdrop)

/-- Every input bit belongs to exactly one prescribed sample word.
The positivity conditions merely ensure that complete-word parsing
retains all scheduled sample rows. -/
theorem prepare_input (c : Context) (markers : List Bool×List Bool)
    (hs : 0 < c.2.1.2) (hr : 0 < ratioWidth c) (ht : 0 < correctionWidth c)
    (bits : Fin (wordWidth c) → Bool) :
    prepare (input c markers bits)=bankInput c markers (wordEquiv c bits) := by
  change ((assignmentCount c,ratioBlocks (input c markers bits)),
    correctionBlock (input c markers bits))=_
  rw [ratioBlocks_input c markers hs hr bits,correctionBlock_input c markers ht bits]
  rfl

end ContingencyTables.RootedEstimatorWordProgram

end OAI
