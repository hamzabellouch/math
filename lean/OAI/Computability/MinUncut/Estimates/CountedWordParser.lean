import Mathlib
import OAI.Computability.MinUncut.Machines.ArenaMachineProgram
import OAI.Computability.MinUncut.Search.CodeLayoutComputable
import OAI.Computability.MinUncut.Machines.FramedWordDecoder

namespace OAI

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial Arena
def finishCounted (v : List ℕ) : List ℕ := v.headI::finish v
def bodyCounted (v : List ℕ) : List ℕ := if symbol v=0 then 0::finishCounted v else 1::step v
noncomputable def finishCountedProgram : PolyProgram finishCounted := PolyProgram.head.cons finishProgram
noncomputable def bodyCountedProgram : PolyProgram bodyCounted :=
  (PolyProgram.branch symbolProgram (PolyProgram.zero.comp finishCountedProgram)
    ((PolyProgram.const 1).cons stepProgram)).ofEq (by intro v; rfl)
def parsedCounted (v : List ℕ) : List ℕ := count v::parsed v
lemma finishCounted_iterate (v : List ℕ) :
    finishCounted (step^[count v] (state 0 0 [] v))=parsedCounted v := by
  have h:=iterate_state v [] v 0 [] (by rfl)
  simpa only [List.length_nil,Nat.zero_add,finishCounted,finish,state,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.headI_cons,parsedCounted,parsed] using congrArg finishCounted h
noncomputable def parserCountedBound : Polynomial ℕ :=
  (X+1)*(bodyCountedProgram.bound.comp parseSize+C 32*(parseSize+3))+C 1000*(X+1)

lemma run_parserCounted (v : List ℕ) :
    Runs (.fix bodyCountedProgram.code) (state 0 0 [] v) (parsedCounted v) (parserCountedBound.eval (magnitude v)) := by
  have hn := (count_le v).trans (length_le_magnitude v)
  have hh:=run_fix_bounded (body:=bodyCountedProgram.code) (out:=parsedCounted v) (state:=fun i=>step^[i] (state 0 0 [] v))
    (count v) (parseSize.eval (magnitude v)) (bodyCountedProgram.bound.eval (parseSize.eval (magnitude v)))
    (iterate_size v) ?_ ?_
  · apply hh.mono
    simp only [parserCountedBound,eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_one,eval_ofNat]
    have h:=Nat.mul_le_mul_right
      (bodyCountedProgram.bound.eval (parseSize.eval (magnitude v))+32*(parseSize.eval (magnitude v)+3))
      (show count v+1≤ magnitude v+1 by omega)
    omega
  · intro i hi
    have hh:=bodyCountedProgram.run (step^[i] (state 0 0 [] v))
    have he : bodyCounted (step^[i] (state 0 0 [] v))=1::step^[i+1] (state 0 0 [] v) := by
      simp only [bodyCounted,symbol_iterate,ite_eq_right (count_drop_ne v i hi),Function.iterate_succ_apply']
    rw [he] at hh
    exact hh.mono (evalNat_mono _ (iterate_size v i (by omega)))
  · have hh:=bodyCountedProgram.run (step^[count v] (state 0 0 [] v))
    have he : bodyCounted (step^[count v] (state 0 0 [] v))=0::parsedCounted v := by
      rw [bodyCounted,symbol_iterate,count_drop_head,ite_eq_left rfl,finishCounted_iterate]
    rw [he] at hh
    exact hh.mono (evalNat_mono _ (iterate_size v (count v) le_rfl))

noncomputable def parserCountedProgram : PolyProgram parsedCounted where
  code := .comp (.fix bodyCountedProgram.code) initializer.code
  bound := parserCountedBound+bodyCountedProgram.bound.comp parseSize+initializer.bound+C 2000*(X+1)
  run v := by
    apply (run_comp (initializer.run v) (run_parserCounted v)).mono
    simp only [eval_add,eval_comp,eval_mul,eval_C,eval_X,eval_one]
    omega
  size v := by
    have hh:=bodyCountedProgram.size (step^[count v] (state 0 0 [] v))
    rw [bodyCounted,symbol_iterate,count_drop_head,ite_eq_left rfl,finishCounted_iterate] at hh
    have hs:=evalNat_mono bodyCountedProgram.bound (iterate_size v (count v) le_rfl)
    simp only [magnitude_cons] at hh
    simp only [eval_add,eval_comp,eval_mul,eval_C,eval_X,eval_one]
    omega

open MinUncutGames.Foundations.Complexity
lemma decodeAux_word (n c : ℕ) (acc : List ℕ) (v : List Bool) :
    decodeAux c acc ((encodeWord n++v).map FrameDecode.symbol)=
      decodeAux 0 ((c+n)::acc) (v.map FrameDecode.symbol) := by
  induction n generalizing c with
  | zero => simp [encodeWord,FrameDecode.symbol,decodeAux]
  | succ n ih =>
    simp only [encodeWord,List.replicate_succ,List.cons_append,List.append_assoc,
      List.map_cons,FrameDecode.symbol,Bool.toNat_true,decodeAux]
    simp only [show ¬(1+1:ℕ)=0 by decide,show ¬(1+1:ℕ)=1 by decide,ite_false,List.nil_append]
    simpa only [encodeWord,List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (c+1)
lemma decodeAux_words (xs acc : List ℕ) :
    decodeAux 0 acc ((encodeWords xs).map FrameDecode.symbol)=xs.reverse++acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    rw [encodeWords,decodeAux_word,Nat.zero_add,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
lemma parsedCounted_words (xs : List ℕ) :
    parsedCounted ((encodeWords xs).map FrameDecode.symbol)=
      (encodeWords xs).length::xs.length::(xs.reverse++(encodeWords xs).map FrameDecode.symbol) := by
  simp only [parsedCounted,FrameDecode.count_symbols,parsed,decodeAux_words,List.append_nil,List.length_reverse,List.cons_append]
end MinUncut.Costed.UnaryWords

noncomputable section
namespace MinUncut.Costed.Arena.Init
open Turing.ToPartrec Polynomial MinUncutGames.Foundations.Complexity

def parseWithKey (v : List ℕ) : List ℕ := v.headI::UnaryWords.parsedCounted v.tail
def parseWithKeyProgram : PolyProgram parseWithKey :=
  PolyProgram.head.cons (UnaryWords.parserCountedProgram.comp PolyProgram.tail)
lemma parseWithKey_spec (K : ℕ) (xs : List ℕ) :
    parseWithKey (K::(encodeWords xs).map FrameDecode.symbol)=
      K::(encodeWords xs).length::xs.length::(xs.reverse++(encodeWords xs).map FrameDecode.symbol) := by
  simp only [parseWithKey,List.headI_cons,List.tail_cons,UnaryWords.parsedCounted_words]

lemma exists_initializer {cs : ℕ → Code} (hc : Computable cs) :
    ∃c : Code,∀K,∃p : Polynomial ℕ,∀xs,
      Runs c (K::(encodeWords xs).map FrameDecode.symbol)
        (initialState (cs K) xs (base (cs K) xs K ((encodeWords xs).map FrameDecode.symbol))).encode
        (p.eval (magnitude (K::(encodeWords xs).map FrameDecode.symbol))) ∧
      magnitude (initialState (cs K) xs (base (cs K) xs K ((encodeWords xs).map FrameDecode.symbol))).encode≤
        p.eval (magnitude (K::(encodeWords xs).map FrameDecode.symbol)) := by
  obtain ⟨c,hc⟩:=FiberPrefix.exists_code (CodeEffective.Layout.c_prefix.comp hc)
  refine ⟨.comp initializer.code (.comp c parseWithKeyProgram.code),fun K=>?_⟩
  obtain ⟨p,hp⟩:=hc K
  let q:=p.comp parseWithKeyProgram.bound
  let r:=parseWithKeyProgram.bound+q+initializer.bound.comp q+2
  refine ⟨r,fun xs=>?_⟩
  let v:=(encodeWords xs).map FrameDecode.symbol
  let w:= (encodeWords xs).length::xs.length::(xs.reverse++v)
  have he:parseWithKey (K::v)=K::w:=parseWithKey_spec K xs
  have hinput: (codeCells (cs K) 0).length::words (codeCells (cs K) 0)++K::w=input (cs K) xs K v := by
    simp only [input,w,v,List.length_map,List.cons_append]
  have hrun:=run_comp (run_comp (parseWithKeyProgram.run (K::v)) (by
    rw [he]
    exact (hp w).1)) (by rw [hinput]; exact initializer.run (input (cs K) xs K v))
  have hs:=parseWithKeyProgram.size (K::v)
  rw [he] at hs
  have hpbound:=evalNat_mono p hs
  have hsize: magnitude (input (cs K) xs K v)≤q.eval (magnitude (K::v)):=by
    have hz:=(hp w).2.trans hpbound
    simpa only [hinput,q,eval_comp] using hz
  have hi:=evalNat_mono initializer.bound hsize
  rw [initializer_spec] at hrun
  dsimp only [v] at *
  constructor
  · apply hrun.mono
    simp only [r,q,eval_add,eval_comp,eval_ofNat]
    simp only [q,eval_comp] at hi
    omega
  · have hz:=initializer.size (input (cs K) xs K v)
    rw [initializer_spec] at hz
    have hz:=hz.trans hi
    dsimp only [v] at hz
    simp only [r,eval_add,eval_comp,eval_ofNat]
    omega
end MinUncut.Costed.Arena.Init

end
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial
noncomputable section
variable {f e : List ℕ → List ℕ}
def untilBody (F : PolyProgram f) (E : PolyProgram e) :
    PolyProgram (fun v=>if (e v).headI=0 then 0::v else 1::f v) :=
  (PolyProgram.branch E ((PolyProgram.const 0).cons PolyProgram.id)
    ((PolyProgram.const 1).cons F)).ofEq (by intro v; rfl)
def untilCode (F : PolyProgram f) (E : PolyProgram e) : Code := .fix (untilBody F E).code

def untilStateBound (L M : ℕ) : Polynomial ℕ := C ((L+1)*(M+1))*(X+1)^2
def untilBound (F : PolyProgram f) (E : PolyProgram e) (L M : ℕ) : Polynomial ℕ :=
  (X+1)*((untilBody F E).bound.comp (untilStateBound L M)+C 32*(untilStateBound L M+3))
lemma iterate_at_stop (hs : ∀v,(e v).headI=0 → f v=v) (v : List ℕ) (i j : ℕ)
    (hi : (e (f^[i] v)).headI=0) (hij : i≤j) : f^[j] v=f^[i] v := by
  have hf : ∀k,f^[k] (f^[i] v)=f^[i] v := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih,hs _ hi]
  rw [show j=(j-i)+i by omega,Function.iterate_add_apply,hf]

lemma run_until (F : PolyProgram f) (E : PolyProgram e) (L M : ℕ)
    (hsize : ∀v,(f v).length≤v.length+L ∧ Arena.maximum (f v)≤Arena.maximum v+M)
    (hstop : ∀v,(e v).headI=0 → f v=v) (v : List ℕ) (B : ℕ)
    (hend : (e (f^[B] v)).headI=0) :
    Runs (untilCode F E) v (f^[B] v) ((untilBound F E L M).eval (magnitude (B::v))) := by
  classical
  let ex : ∃i,(e (f^[i] v)).headI=0 := ⟨B,hend⟩
  let n := Nat.find ex
  have hn : n≤B := Nat.find_min' ex hend
  have hdone : (e (f^[n] v)).headI=0 := Nat.find_spec ex
  let Z := (untilStateBound L M).eval (magnitude (B::v))
  have hm : ∀i≤B,magnitude (f^[i] v)≤Z := by
    intro i hi
    simpa only [Z, untilStateBound, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] using Arena.iterate_magnitude L M hsize B v i hi
  have he : f^[B] v=f^[n] v := iterate_at_stop hstop v n B hdone hn
  have hb : ∀i≤B,Runs (untilBody F E).code (f^[i] v)
      (if (e (f^[i] v)).headI=0 then 0::f^[i] v else 1::f^[i+1] v)
      ((untilBody F E).bound.eval Z) := by
    intro i hi
    have hh := ((untilBody F E).run (f^[i] v)).mono (evalNat_mono _ (hm i hi))
    simpa only [Function.iterate_succ_apply'] using hh
  have hr := run_fix_bounded n Z ((untilBody F E).bound.eval Z)
    (fun i hi=>hm i (hi.trans hn)) (state:=fun i=>f^[i] v) (out:=f^[n] v)
    (by intro i hi; simpa only [ite_eq_right (Nat.find_min ex hi)] using hb i (by omega))
    (by simpa only [hdone,ite_true] using hb n hn)
  rw [←he] at hr
  apply hr.mono
  have hn' : n+1 ≤ magnitude (B::v)+1 := by simp only [magnitude_cons]; omega
  have hp := Nat.mul_le_mul_right ((untilBody F E).bound.eval Z+32*(Z+3)) hn'
  simpa only [untilBound,eval_mul,eval_add,eval_comp,eval_X,eval_one,eval_C,eval_ofNat,Z] using hp
end
end MinUncut.Costed

namespace MinUncut.Costed.Arena
open Turing.ToPartrec Polynomial
noncomputable section

def stoppedTick (v : List ℕ) : List ℕ := if v.headI=2 then v else rawTick v
def stopExpr : Expr := .sub (.const 1) (.eq (.reg 0) (.const 2))
def stopProgram : PolyProgram (fun v=>[stopExpr.eval v]) := stopExpr.program
def stoppedTickProgram : PolyProgram stoppedTick :=
  (PolyProgram.branch stopProgram PolyProgram.id tickProgram).ofEq (by
    intro v
    simp only [stopExpr,Expr.eval,List.headI_cons,stoppedTick,List.drop_zero]
    by_cases h:v.headI=2 <;> simp only [h,ite_true,ite_false,Nat.sub_self,Nat.sub_zero,Nat.one_ne_zero])
lemma stop_zero (v : List ℕ) : stopExpr.eval v=0 ↔ v.headI=2 := by
  simp only [stopExpr,Expr.eval,List.drop_zero]
  split_ifs <;> simp_all
lemma stoppedTick_safe (v : List ℕ) :
    (stoppedTick v).length≤v.length+9 ∧ maximum (stoppedTick v)≤ maximum v+3 := by
  unfold stoppedTick
  split_ifs
  · exact ⟨by omega,by omega⟩
  · exact rawTick_safe v
lemma stoppedTick_encode (s : State) : stoppedTick s.encode=(s.tick).encode := by
  by_cases h:s.mode=2
  · simp only [stoppedTick,State.encode,List.cons_append,List.nil_append,List.headI_cons,h,ite_true]
    have hs : s.tick=s := by simp [State.tick,h]
    rw [hs]
    simp only [h]
  · rw [stoppedTick,ite_eq_right (show s.encode.headI≠2 from h),rawTick_encode]
lemma stoppedTick_iter_encode (s : State) (i : ℕ) : stoppedTick^[i] s.encode=rawTick^[i] s.encode := by
  have hh (s : State) (i : ℕ) : stoppedTick^[i] s.encode=(State.tick^[i] s).encode ∧
      rawTick^[i] s.encode=(State.tick^[i] s).encode := by
    induction i with
    | zero => exact ⟨rfl,rfl⟩
    | succ i ih =>
      constructor <;> rw [Function.iterate_succ_apply']
      · rw [ih.1,stoppedTick_encode,Function.iterate_succ_apply']
      · rw [ih.2,rawTick_encode,Function.iterate_succ_apply']
  exact (hh s i).1.trans (hh s i).2.symm

def unboundedControl : Code := untilCode stoppedTickProgram stopProgram
lemma unboundedControl_run {c v w B} (hr : Runs c v w B) (base : Heap) :
    ∃h out,ListRep h out w ∧
      magnitude (State.mk 2 0 out 0 h).encode ≤
        (untilStateBound 9 3).eval (magnitude ((3*B+1)::(initialState c v base).encode)) ∧
      Runs unboundedControl (initialState c v base).encode (State.mk 2 0 out 0 h).encode
        ((untilBound stoppedTickProgram stopProgram 9 3).eval
          (magnitude ((3*B+1)::(initialState c v base).encode))) := by
  obtain ⟨t,ht,hc⟩:=hr
  obtain ⟨h,out,ho,he⟩:=CodeRun.interpreted hc base ht
  rw [←stoppedTick_iter_encode] at he
  refine ⟨h,out,ho,?_,?_⟩
  · rw [←he]
    simpa only [untilStateBound,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      iterate_magnitude 9 3 stoppedTick_safe (3*B+1) (initialState c v base).encode (3*B+1) le_rfl
  have hh:=run_until stoppedTickProgram stopProgram 9 3 stoppedTick_safe
    (by intro u hu; change stopExpr.eval u=0 at hu; simp [stoppedTick,(stop_zero u).mp hu])
    (initialState c v base).encode (3*B+1)
    (by rw [he]; change stopExpr.eval _=0; exact (stop_zero _).mpr rfl)
  simpa only [he,unboundedControl] using hh

def prepareUnbounded (v : List ℕ) : List ℕ :=
  [(r 2).eval v,(r 4).eval v,0,2]++v.drop 5
def prepareUnboundedProgram : PolyProgram prepareUnbounded :=
  (r 2).program.cons ((r 4).program.cons ((c 0).program.cons ((c 2).program.cons (PolyProgram.drop 5))))
def unboundedOutput : Code := untilCode outputStepProgram PolyProgram.head
lemma unboundedOutput_run {h p w} (ho : ListRep h p w) (B : ℕ) (hw : w.length≤B) :
    Runs unboundedOutput (OutputState.mk p h []).encode (OutputState.mk 0 h w.reverse).encode
      ((untilBound outputStepProgram PolyProgram.head 4 1).eval
        (magnitude (B::(OutputState.mk p h []).encode))) := by
  have he := ho.output_padded [] hw
  simp only [List.append_nil] at he
  have hh:=run_until outputStepProgram PolyProgram.head 4 1 outputStep_safe
    (by intro u hu; change u.headI=0 at hu; simp [outputStep,hu])
    (OutputState.mk p h []).encode B
    (by rw [he]; rfl)
  simpa only [he,unboundedOutput] using hh

def unboundedWordsCode : Code :=
  .comp reversePrefixProgram.code
    (.comp (PolyProgram.drop 2).code
      (.comp unboundedOutput (.comp prepareUnboundedProgram.code unboundedControl)))

end

open Turing.ToPartrec Polynomial
noncomputable section

def unboundedControllerInput : Polynomial ℕ := 3*X+2
def unboundedControllerState : Polynomial ℕ := (untilStateBound 9 3).comp unboundedControllerInput
def unboundedPrepared : Polynomial ℕ := prepareUnboundedProgram.bound.comp unboundedControllerState
def unboundedOutputInput : Polynomial ℕ := X+unboundedPrepared+1
def unboundedOutputState : Polynomial ℕ := (untilStateBound 4 1).comp unboundedOutputInput
def unboundedDropped : Polynomial ℕ := (PolyProgram.drop 2).bound.comp unboundedOutputState
def unboundedWordsBound : Polynomial ℕ :=
  (untilBound stoppedTickProgram stopProgram 9 3).comp unboundedControllerInput+
  unboundedPrepared+(untilBound outputStepProgram PolyProgram.head 4 1).comp unboundedOutputInput+
  unboundedDropped+reversePrefixProgram.bound.comp unboundedDropped+4

lemma unboundedWords_run {c v w B} (hr : Runs c v w B) (hl : w.length≤B) (base : Heap) :
    ∃h,Runs unboundedWordsCode (initialState c v base).encode (w++w.reverse++2::words h)
      (unboundedWordsBound.eval (magnitude (B::(initialState c v base).encode))) ∧
      magnitude (w++w.reverse++2::words h)≤
        unboundedWordsBound.eval (magnitude (B::(initialState c v base).encode)) := by
  let M:=magnitude (B::(initialState c v base).encode)
  have hci : magnitude ((3*B+1)::(initialState c v base).encode)≤unboundedControllerInput.eval M := by
    simp only [unboundedControllerInput,eval_add,eval_mul,eval_X,eval_ofNat,M,magnitude_cons]
    omega
  obtain ⟨h,out,ho,hm0,hr0⟩:=unboundedControl_run hr base
  have hm : magnitude (State.mk 2 0 out 0 h).encode≤unboundedControllerState.eval M :=
    by simpa only [unboundedControllerState,eval_comp] using hm0.trans (evalNat_mono _ hci)
  have hc := hr0.mono (evalNat_mono _ hci)
  have hp := (prepareUnboundedProgram.run (State.mk 2 0 out 0 h).encode).mono (evalNat_mono _ hm)
  have hps := (prepareUnboundedProgram.size (State.mk 2 0 out 0 h).encode).trans (evalNat_mono _ hm)
  have hprep : prepareUnbounded (State.mk 2 0 out 0 h).encode=(OutputState.mk out h []).encode := by
    simp only [prepareUnbounded,State.encode,OutputState.encode,Expr.eval,List.cons_append,
      List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons]
    rfl
  rw [hprep] at hp hps
  have hp' : Runs prepareUnboundedProgram.code (State.mk 2 0 out 0 h).encode (OutputState.mk out h []).encode (unboundedPrepared.eval M) := by
    simpa only [unboundedPrepared,eval_comp] using hp
  have hps' : magnitude (OutputState.mk out h []).encode≤unboundedPrepared.eval M := by
    simpa only [unboundedPrepared,eval_comp] using hps
  have hB : B≤M := by simp only [M,magnitude_cons]; omega
  have hoi : magnitude (B::(OutputState.mk out h []).encode)≤unboundedOutputInput.eval M := by
    simp only [unboundedOutputInput,eval_add,eval_X,eval_one,magnitude_cons]
    omega
  have hout := (unboundedOutput_run ho B hl).mono (evalNat_mono _ hoi)
  have hes := ho.output_padded [] hl
  simp only [List.append_nil] at hes
  have hos : magnitude (OutputState.mk 0 h w.reverse).encode≤unboundedOutputState.eval M := by
    have hh := iterate_magnitude 4 1 outputStep_safe B (OutputState.mk out h []).encode B le_rfl
    rw [hes] at hh
    have hh' : magnitude (OutputState.mk 0 h w.reverse).encode≤
        (untilStateBound 4 1).eval (magnitude (B::(OutputState.mk out h []).encode)) := by
      simpa only [untilStateBound,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one] using hh
    simpa only [unboundedOutputState,eval_comp] using hh'.trans (evalNat_mono _ hoi)
  have hd := ((PolyProgram.drop 2).run (OutputState.mk 0 h w.reverse).encode).mono (evalNat_mono _ hos)
  have hds := ((PolyProgram.drop 2).size (OutputState.mk 0 h w.reverse).encode).trans (evalNat_mono _ hos)
  have hv := (reversePrefixProgram.run ((OutputState.mk 0 h w.reverse).encode.drop 2)).mono (evalNat_mono _ hds)
  have hvs := (reversePrefixProgram.size ((OutputState.mk 0 h w.reverse).encode.drop 2)).trans (evalNat_mono _ hds)
  have he : (prefixStep^[((OutputState.mk 0 h w.reverse).encode.drop 2).headI]
      (0::((OutputState.mk 0 h w.reverse).encode.drop 2).tail)).tail=w++w.reverse++2::words h := by
    change (prefixStep^[w.reverse.length] (0::(w.reverse++2::words h))).tail=_
    rw [reversePrefix_spec,List.reverse_reverse]
  rw [he] at hv hvs
  dsimp only [M] at *
  refine ⟨h,?_,?_⟩
  · apply (run_comp (run_comp (run_comp (run_comp hc hp') hout) hd) hv).mono
    simp only [unboundedWordsBound,eval_add,eval_comp,eval_ofNat,unboundedPrepared,
      unboundedDropped,unboundedControllerState,unboundedOutputState]
    omega
  · apply hvs.trans
    simp only [unboundedWordsBound,unboundedPrepared,unboundedDropped,unboundedControllerState,
      unboundedOutputState,eval_add,eval_comp,eval_ofNat]
    omega
end
end MinUncut.Costed.Arena

end OAI
