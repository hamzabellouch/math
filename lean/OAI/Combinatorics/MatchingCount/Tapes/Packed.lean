import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeListMore
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Tapes.Codec

namespace OAI

namespace MatchingFPRAS.LiteralPacked
open TreeTyped TreeData TreeFunction TreeMachine TreePost

abbrev Row := K Reg→Option Bool
def baseRow : Row
  | .inl _ => some false
  | .inr _ => none
def bitRow (b : Bool) : Row := fun k=>if k=Sum.inl 0 then some b else none
def bottom : Alphabet := (true,baseRow)
def letter (b : Bool) : Alphabet := (false,bitRow b)
lemma rows_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.rows (inputStacks a) (weight a)=baseRow::bs.map bitRow := by
  have hw : weight a=bs.length+1 := by
    have h:=congrArg List.length hs
    simpa only [List.length_reverse,List.length_cons,weight,TreeFunction.size] using h
  apply List.ext_getElem
  · simp only [StackWords.rows,List.length_ofFn,List.length_cons,List.length_map,hw]
  · intro i hi hj
    simp only [StackWords.rows,List.getElem_ofFn]
    funext k
    cases k with
    | inr k =>
      cases i <;> simp [inputStacks,encodeEnv,baseRow,bitRow]
    | inl r =>
      by_cases hr:r=0
      · subst r
        simp only [inputStacks,encodeEnv,env,ite_true,hs]
        cases i <;> simp [baseRow,bitRow]
      · have hn : env (TreeTyped.encode a) .nil .nil r=.nil := by simp [env,hr]
        simp only [inputStacks,encodeEnv,hn,TreeData.encode,List.reverse_singleton]
        cases i <;> simp [baseRow,bitRow,hr]
lemma word_eq {A : Type} [Codec A] (a : A) (bs : List Bool)
    (hs : (TreeData.encode (TreeTyped.encode a)).reverse=false::bs) :
    StackWords.word (inputStacks a) (weight a)=bottom::bs.map letter := by
  rw [StackWords.word,rows_eq a bs hs]
  simp only [List.headI_cons,List.tail_cons]
  change (true,baseRow)::(bs.map bitRow).map (fun a=>(false,a)) = (true,baseRow)::bs.map LiteralPacked.letter
  rw [List.map_map]
  rfl

def symbolBits (a : Symbol) : List Bool := (TreeData.encode (TreeTyped.encode a)).reverse++[true]
lemma symbolBits_length (a : Symbol) : (symbolBits a).length=18 := by
  simp only [symbolBits,List.length_append,List.length_reverse,List.length_singleton]
  change weight a+1=18
  rw [LiteralCodec.weight_symbol]
lemma list_bits (as : List Symbol) :
    (TreeData.encode (TreeTyped.encode as)).reverse=false::as.reverse.flatMap symbolBits := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [TreeTyped.encode_list_cons,TreeData.encode,List.reverse_cons,List.reverse_append,ih,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,symbolBits,
      List.cons_append,List.append_assoc]

noncomputable def block (a : Alphabet) : List Symbol :=
  (FixedEncoding.enc Alphabet a).toList.map BoolPostCompiler.up
noncomputable def header : List Symbol := block bottom
noncomputable def chunk (a : Symbol) : List Symbol := (symbolBits a).flatMap (fun b=>block (letter b))
noncomputable def width : ℕ := Fintype.card Alphabet
lemma map_enc_length {α : Type} [Fintype α] [Inhabited α] (a : α) :
    ((FixedEncoding.enc α a).toList.map BoolPostCompiler.up).length=Fintype.card α := by
  rw [List.length_map]
  exact (FixedEncoding.enc α a).2
lemma block_length (a : Alphabet) : (block a).length=width := by
  unfold width block
  exact map_enc_length a
lemma flatMap_uniform_length {α β : Type} (as : List α) (f : α→List β) (w : ℕ)
    (h : ∀ a,(f a).length=w) : (as.flatMap f).length=as.length*w := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons,List.length_append,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul];omega
lemma chunk_length (a : Symbol) : (chunk a).length=18*width := by
  exact (flatMap_uniform_length (symbolBits a) (fun b=>block (letter b)) width
    (fun b=>block_length (letter b))).trans (congrArg (fun n=>n*width) (symbolBits_length a))

lemma packed_eq (as : List Symbol) : TreePost.packed as=header++as.reverse.flatMap chunk := by
  unfold TreePost.packed StackWords.encoded FixedAlphabetCompiler.word FixedAlphabetCompiler.bitsWord
  rw [word_eq as _ (list_bits as)]
  simp only [List.flatMap_cons,List.map_append,List.flatMap_map,List.map_flatMap,
    List.flatMap_assoc,LiteralPacked.header,LiteralPacked.block]
  rfl
lemma block_alphabet (a : Alphabet) (s : Symbol) (hs : s∈block a) : s=0 ∨ s=1 := by
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
  cases b <;> simp [BoolPostCompiler.up]
lemma chunk_alphabet (a s : Symbol) (hs : s∈chunk a) : s≠6 ∧ s≠7 := by
  obtain ⟨b,_,hb⟩:=List.mem_flatMap.mp hs
  rcases block_alphabet _ _ hb with rfl|rfl <;> decide
end MatchingFPRAS.LiteralPacked

end OAI
