import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.PackedExecution
import OAI.Combinatorics.MatchingCount.Machines.OnlinePhysicalProgram
import OAI.Combinatorics.MatchingCount.Machines.PhysicalProgramMap
import OAI.Combinatorics.MatchingCount.Algorithm.Algorithm
import OAI.Combinatorics.MatchingCount.Complexity.OnlineCost

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped

noncomputable def pack : Program := Program.ofTM1 packCode .start (fun _=>0)
noncomputable def erase : Program := Program.ofTM1 (LiteralTape.eraseCode header.length) () ()
noncomputable def unpack : Program := Program.ofTM1 unpackCode .start (fun _=>0)
noncomputable def post : Program := erase.seq unpack
noncomputable def packTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget 1 (18*width) n 0)*MachineCost.programCost packCode
noncomputable def eraseTime : ℕ := MachineCost.programCost (LiteralTape.eraseCode header.length)
noncomputable def unpackTime (n : ℕ) : ℕ :=
  (1+LiteralBlockMap.budget (18*width) 1 n 0)*MachineCost.programCost unpackCode
noncomputable def postTime (n : ℕ) : ℕ := eraseTime+unpackTime n
lemma packTime_mono {n m : ℕ} (h : n ≤ m) : packTime n ≤ packTime m := by
  unfold packTime LiteralBlockMap.budget;gcongr
lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime unpackTime LiteralBlockMap.budget;gcongr
lemma pack_realizes (as : List Symbol) (ha : ∀ a∈as,a≠0) :
    pack.Realizes (Tape.mk₁ as) (.done (Tape.mk₁ (TreePost.packed as))) (packTime as.length) :=
  Program.realizes_TM1 _ _ _ _ _ _ _ (pack_exec as ha)
lemma post_realizes (as : List Symbol) (ha : ∀ a∈as,a≠6 ∧ a≠7) :
    post.Realizes (Tape.mk₁ (TreePost.packed as)) (.done (Tape.mk₁ as)) (postTime as.length) := by
  have h1 : erase.Realizes (Tape.mk₁ (TreePost.packed as))
      (.done (Tape.mk₁ (as.reverse.flatMap chunk))) eraseTime := by
    rw [packed_eq]
    exact (Program.realizes_TM1 _ _ _ _ _ _ _ (LiteralTape.erase_exec header (as.reverse.flatMap chunk))).mono
      (by simp only [Nat.one_mul];rfl)
  have h2 : unpack.Realizes (Tape.mk₁ (as.reverse.flatMap chunk)) (.done (Tape.mk₁ as)) (unpackTime as.length) :=
    Program.realizes_TM1 _ _ _ _ _ _ _ (unpack_exec as ha)
  exact Program.seq_realizes erase unpack _ (.done (Tape.mk₁ (as.reverse.flatMap chunk)))
    (fun _=>.done (Tape.mk₁ as)) _ _ h1 h2

noncomputable def wrap {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f) : Program :=
  (pack.seq (OnlineTree.physicalProgram F)).seq post
noncomputable def wrapTime {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f)
    (as : List Symbol) : ℕ := packTime as.length+OnlineTree.physicalCost F as+postTime ((f as).worst List.length)
lemma wrap_realizes {f : List Symbol→Experiment (List Symbol)} (F : OnlineTree.Realizer f)
    (as : List Symbol) (ha : ∀ a∈as,a≠0) (hout : (f as).All (fun bs=>∀ b∈bs,b≠6 ∧ b≠7)) :
    (wrap F).Realizes (Tape.mk₁ as) ((f as).map Tape.mk₁) (wrapTime F as) := by
  have h1 : (pack.seq (OnlineTree.physicalProgram F)).Realizes (Tape.mk₁ as)
      ((f as).map (fun bs=>Tape.mk₁ (TreePost.packed bs))) (packTime as.length+OnlineTree.physicalCost F as) :=
    Program.seq_realizes pack (OnlineTree.physicalProgram F) _ (.done (Tape.mk₁ (TreePost.packed as)))
      (fun _=>(f as).map (fun bs=>Tape.mk₁ (TreePost.packed bs))) _ _ (pack_realizes as ha) (OnlineTree.physical_realizes F as)
  exact Program.seq_realizes_map _ _ _ (f as) (fun bs=>Tape.mk₁ (TreePost.packed bs)) (fun bs=>.done (Tape.mk₁ bs))
    _ _ h1 ((hout.and (Experiment.all_worst (f as) List.length)).mono
      (fun bs hbs=>(post_realizes bs hbs.1).mono (postTime_mono hbs.2)))

lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide
lemma encodeRat_nonzero (q : ℚ) (a : Symbol) (ha : a∈encodeRat q) : a≠0 := by
  simp only [encodeRat,encodeInt,List.mem_append] at ha
  rcases ha with (ha|ha)|ha
  · split_ifs at ha with hn <;> simp only [List.mem_singleton] at ha <;> subst a <;> decide
  · exact encodeNat_nonzero _ _ ha
  · exact encodeNat_nonzero _ _ ha
lemma input_nonzero (G : GraphInput) (ε δ : ℚ) (a : Symbol) (ha : a∈encodeInput G ε δ) : a≠0 := by
  simp only [encodeInput,List.mem_append] at ha
  rcases ha with (((ha|ha)|ha)|ha)|ha
  · exact encodeNat_nonzero _ _ ha
  · exact encodeNat_nonzero _ _ ha
  · obtain ⟨e,_,he⟩:=List.mem_flatMap.mp ha
    rcases List.mem_append.mp he with he|he <;> exact encodeNat_nonzero _ _ he
  · exact encodeRat_nonzero _ _ ha
  · exact encodeRat_nonzero _ _ ha
lemma natWord_alphabet (n : ℕ) (a : Symbol) (ha : a∈LiteralCodec.natWord n) : a≠6 ∧ a≠7 := by
  simp only [LiteralCodec.natWord,LiteralCodec.fromBit,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide
lemma ratWord_alphabet (q : TreeFraction.Fraction) (a : Symbol) (ha : a∈LiteralCodec.ratWord q) : a≠6 ∧ a≠7 := by
  simp only [LiteralCodec.ratWord,List.mem_cons,List.mem_append] at ha
  rcases ha with (rfl|ha)|ha
  · decide
  · exact natWord_alphabet _ _ ha
  · exact natWord_alphabet _ _ ha
lemma algorithm_alphabet (as : List Symbol) :
    (LiteralAlgorithm.algorithm as).All (fun bs=>∀ b∈bs,b≠6 ∧ b≠7) := by
  rw [LiteralAlgorithm.algorithm,Experiment.all_map]
  exact (Experiment.all_true _).mono (fun q _=>ratWord_alphabet q)
noncomputable def mainProgram : Program := wrap LiteralAlgorithm.algorithmRealizer
lemma mainProgram_realizes (G : GraphInput) (ε δ : ℚ) :
    mainProgram.Realizes (Tape.mk₁ (encodeInput G ε δ))
      ((LiteralAlgorithm.algorithm (encodeInput G ε δ)).map Tape.mk₁)
      (wrapTime LiteralAlgorithm.algorithmRealizer (encodeInput G ε δ)) :=
  wrap_realizes _ _ (input_nonzero G ε δ) (algorithm_alphabet _)
end MatchingFPRAS.LiteralPhysical

end OAI
