import Mathlib
import OAI.Combinatorics.KMedian.Process.RoundingUniformStep

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

def vectorData {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) : Data Row :=
  ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)

theorem vectorData_branch {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n))
    (p : Vector ℚ n → ℚ) (hp : ∀ q, 0≤p q ∧ p q≤1) (next : Vector ℚ n → Fin 2 → Vector ℚ n)
    (P : Row → ℚ) (E0 E1 : Row → Row)
    (hP : ∀ q, P q.toList=p q) (hE0 : ∀ q, E0 q.toList=(next q 0).toList)
    (hE1 : ∀ q, E1 q.toList=(next q 1).toList) :
    (branchLawData ((vectorData μ).1,(vectorData μ).2.map P),
      (vectorData μ).2.flatMap (fun q => [E0 q,E1 q]))=vectorData (μ.branch p hp next) := by
  simp only [vectorData,states_list,List.map_ofFn,Function.comp_def,hP]
  rw [branchLaw_ofFn μ.law _ (fun i => hp μ.states[i.val])]
  congr 1
  simp only [SparseIntegerLaw.branch,Vector.getElem_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def,hE0,hE1]
  exact (two_expand (fun i b => (next μ.states[i.val] b).toList)).symm

theorem branch_raw (s : Bool) (x : State s) :
    (x.raw.1,(branchLawData (x.raw.2.1,x.raw.2.2.map (fun p => probability s (x.raw.1,p))),
      x.raw.2.2.flatMap (fun p => [endpoint s false (x.raw.1,p),endpoint s true (x.raw.1,p)])))=
       x.branch.raw := by
  cases s
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalWeightedStep.probability x.β)
        (RationalWeightedStep.probability_unit x.β (x.positive rfl)) (RationalWeightedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.probability (List.ofFn x.β))
      (fun p => RoundingList.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.endpoint (List.ofFn x.β) p true)
      (RoundingList.probability_list x.β)
      (fun p => RoundingList.endpoint_list x.β p 0) (fun p => RoundingList.endpoint_list x.β p 1)
  · change (List.ofFn x.β,_)=(List.ofFn x.β,vectorData
      (x.μ.branch (RationalSignedStep.probability x.β)
        (RationalSignedStep.probability_unit x.β) (RationalSignedStep.endpoint x.β)))
    apply congrArg (fun d => (List.ofFn x.β,d))
    exact vectorData_branch x.μ _ _ _ (RoundingList.Signed.probability (List.ofFn x.β))
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p false)
      (fun p => RoundingList.Signed.endpoint (List.ofFn x.β) p true)
      (RoundingList.Signed.probability_list x.β)
      (fun p => RoundingList.Signed.endpoint_list x.β p 0) (fun p => RoundingList.Signed.endpoint_list x.β p 1)

noncomputable def branchProgram (s : Bool) : PolyProgram State.encode State.encode (@State.branch s) :=
  (branchRawProgram s).recode State.raw State.encode_raw (fun x => by
    rw [branch_raw,State.encode_raw])

noncomputable def compressionInputProgram (s : Bool) :
    PolyProgram State.encode IntegerLaw.BinaryCompression.RationalInput.encode (@State.compressionInput s) := by
  let β := fst erow (ed erow)
  let law := (snd erow (ed erow)).comp (fst el (encodeList erow))
  let states := (snd erow (ed erow)).comp (snd el (encodeList erow))
  let dims := β.comp RoundingList.dimensions_poly.program
  let feats := states.comp (RoundingList.features_poly.program.listMap [])
  let work := dims.fanout (law.fanout feats)
  exact work.recode State.raw State.encode_raw (fun x => by
    change IntegerLaw.BinaryCompression.eqd
      (RoundingList.dimensions (List.ofFn x.β),
       ((x.μ.law.denominator,List.ofFn x.μ.law.numerator),
        (x.μ.states.toList.map Vector.toList).map RoundingList.features))=_
    simp only [RoundingList.dimensions_list,states_list,List.map_ofFn,Function.comp_def,RoundingList.features_list]
    rfl)

noncomputable def statesProgram (s : Bool) :
    PolyProgram State.encode (encodeList erow) (fun x : State s => x.μ.states.toList.map Vector.toList) :=
  ((snd erow (ed erow)).comp (snd el (encodeList erow))).recode State.raw State.encode_raw (fun _ => rfl)
noncomputable def weightsProgram (s : Bool) :
    PolyProgram State.encode erow (fun x : State s => List.ofFn x.β) :=
  (fst erow (ed erow)).recode State.raw State.encode_raw (fun _ => rfl)

theorem trimData_map {α β : Type} (f : α → β) (d : Data α) :
    trimData (d.1,d.2.map f)=((trimData d).1,(trimData d).2.map f) := by
  have hz : d.1.2.zip (d.2.map f)=(d.1.2.zip d.2).map (fun z => (z.1,f z.2)) := by
    exact List.zip_map_right
  simp only [trimData,activeEntries,hz,List.filter_map,List.map_map,Function.comp_def]

theorem trim_encode_raw {n : ℕ} (μ : SparseIntegerLaw (Vector ℚ n)) :
    trimData ((μ.law.denominator,List.ofFn μ.law.numerator),μ.states.toList.map Vector.toList)=
      (((μ.trim).law.denominator,List.ofFn (μ.trim).law.numerator),μ.trim.states.toList.map Vector.toList) := by
  change trimData ((raw μ).1,(raw μ).2.map Vector.toList)=_
  rw [trimData_map,trimData_raw]
  rfl

noncomputable def compressProgram (s : Bool) : PolyProgram State.encode State.encode (@State.compress s) := by
  let law := (compressionInputProgram s).comp IntegerLaw.BinaryCompression.rationalCompressProgram
  let trimmed := (law.fanout (statesProgram s)).comp (trimDataProgram erow [])
  let work := (weightsProgram s).fanout trimmed
  exact work.recode id (fun _ => rfl) (fun x => by
    change encodePair erow (ed erow) (List.ofFn x.β,
      trimData (((x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])).denominator,
       List.ofFn (x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])).numerator),
         x.μ.states.toList.map Vector.toList))=_
    rw [show trimData _= _ from trim_encode_raw
      (⟨x.μ.length,x.μ.states,x.μ.law.compressAuto (fun i => SparseWeightedPartial.features x.μ.states[i.val])⟩ : SparseIntegerLaw (Vector ℚ x.n))]
    exact State.encode_raw x.compress)

noncomputable def stepProgram (s : Bool) : PolyProgram State.encode State.encode (@State.step s) :=
  (branchProgram s).comp (compressProgram s)

end MetricKMedian.RoundingProgram
end

end OAI
