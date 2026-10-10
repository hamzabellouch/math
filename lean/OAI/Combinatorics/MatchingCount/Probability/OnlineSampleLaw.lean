import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.OnlineUniform
import OAI.Combinatorics.MatchingCount.Sampling.OnlineSample

namespace OAI

namespace MatchingFPRAS.OnlineSample
open PhysicalStream

abbrev LocalRandom (N k : ℕ) := Bits k × (Fin N → Bits k)
abbrev ScanRandom (N k : ℕ) := Bits k × LocalRandom N k
def localRep {N k : ℕ} (b : LocalRandom N k) : NumericLadder.Bits :=
  (List.ofFn b.1,List.ofFn (fun i=>List.ofFn (b.2 i)))
def scanRep {N k : ℕ} (b : ScanRandom N k) : List Bool×NumericLadder.Bits :=
  (List.ofFn b.1,localRep b.2)
lemma mean_words (k N : ℕ) (h : List (List Bool) → ℚ) :
    (words (k,N)).mean h=qaverage (fun bs : Fin N → Bits k=>h (List.ofFn (fun i=>List.ofFn (bs i)))) := by
  unfold words
  rw [show List.replicate N k=List.ofFn (fun _ : Fin N=>k) by simp]
  exact mean_traverse_ofFn word N (fun _=>k) (fun _ b=>List.ofFn b) (fun _=>mean_word_qaverage k) h
lemma mean_local (k N : ℕ) (h : NumericLadder.Bits → ℚ) :
    (localWords (k,N)).mean h=qaverage (fun bs : LocalRandom N k=>h (localRep bs)) := by
  simp only [localWords,Experiment.mean_bind,Experiment.mean_map,mean_words,mean_word_qaverage]
  rw [qaverage_prod]
  rfl
lemma mean_scan (k N : ℕ) (h : List Bool×NumericLadder.Bits → ℚ) :
    (scan (k,N)).mean h=qaverage (fun bs : ScanRandom N k=>h (scanRep bs)) := by
  simp only [scan,Experiment.mean_bind,Experiment.mean_map,mean_local,mean_word_qaverage]
  rw [qaverage_prod]
  rfl
lemma mean_scans (k N r : ℕ) (h : List (List Bool×NumericLadder.Bits) → ℚ) :
    (scans ((k,N),r)).mean h=qaverage (fun bs : Fin r→ScanRandom N k=>h (List.ofFn (fun i=>scanRep (bs i)))) := by
  unfold scans
  rw [show List.replicate r (k,N)=List.ofFn (fun _ : Fin r=>(k,N)) by simp]
  exact mean_traverse_ofFn scan r (fun _=>(k,N)) (fun _ b=>scanRep b) (fun _=>mean_scan k N) h
lemma mean_marks (km m : ℕ) (keys : Fin m→ℕ) (h : List (ℕ×List Bool) → ℚ) :
    (marks (km,List.ofFn keys)).mean h=
      qaverage (fun bs : Fin m→Bits km=>h (List.ofFn (fun i=>(keys i,List.ofFn (bs i))))) := by
  simp only [marks,markRequests,List.map_ofFn]
  apply mean_traverse_ofFn markWord m (fun i=>(keys i,km)) (fun i b=>(keys i,List.ofFn b))
  intro i h
  simp only [markWord,Experiment.mean_map,mean_word_qaverage]

abbrev Random (N k r m km : ℕ) := (Fin r→ScanRandom N k)×(Fin m→Bits km)
def sampleRep {N k r m km : ℕ} (keys : Fin m→ℕ) (bs : Random N k r m km) : NumericMarking.SampleBits :=
  (List.ofFn (fun i=>scanRep (bs.1 i)),List.ofFn (fun i=>(keys i,List.ofFn (bs.2 i))))
lemma mean_sample (N k r m km : ℕ) (keys : Fin m→ℕ) (h : NumericMarking.SampleBits → ℚ) :
    (sample (((k,N),r),(km,List.ofFn keys))).mean h=
      qaverage (fun bs : Random N k r m km=>h (sampleRep keys bs)) := by
  simp only [sample,Experiment.mean_bind,Experiment.mean_map,mean_marks,mean_scans]
  rw [qaverage_prod]
  rfl
lemma mean_many (S N k r m km : ℕ) (keys : Fin m→ℕ) (h : List NumericMarking.SampleBits → ℚ) :
    (many (S,(((k,N),r),(km,List.ofFn keys)))).mean h=
      qaverage (fun bs : Fin S→Random N k r m km=>h (List.ofFn (fun i=>sampleRep keys (bs i)))) := by
  unfold many
  rw [show List.replicate S (((k,N),r),(km,List.ofFn keys))=
    List.ofFn (fun _ : Fin S=>(((k,N),r),(km,List.ofFn keys))) by simp]
  exact mean_traverse_ofFn sample S (fun _=>(((k,N),r),(km,List.ofFn keys)))
    (fun _ b=>sampleRep keys b) (fun _=>mean_sample N k r m km keys) h
end MatchingFPRAS.OnlineSample

end OAI
