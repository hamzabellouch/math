import Mathlib
import OAI.Computability.MinUncut.Estimates.CodeContinuations

namespace OAI

section
namespace MinUncut.Costed.Arena

def keepTick (v : List ℕ) : List ℕ := v.headI::rawTick v.tail
noncomputable def keepTickProgram : PolyProgram keepTick :=
  PolyProgram.head.cons (tickProgram.comp PolyProgram.tail)

lemma keepTick_safe (v : List ℕ) :
    (keepTick v).length≤v.length+10 ∧ maximum (keepTick v)≤ maximum v+3 := by
  have hh := rawTick_safe v.tail
  have ht : v.tail=v.drop 1 := (List.drop_one (l := v)).symm
  have hm := maximum_drop v 1
  have hl : v.tail.length≤v.length := by cases v <;> simp
  have he := head_le_maximum v
  rw [←ht] at hm
  simp only [keepTick,List.length_cons,maximum_cons]
  constructor
  · omega
  · exact max_le (by omega) (by omega)

lemma keepTick_iter (B i : ℕ) (v : List ℕ) :
    keepTick^[i] (B::v)=B::rawTick^[i] v := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih];
                 change B::rawTick (rawTick^[i] v)=_; rw [Function.iterate_succ_apply']

def control (v : List ℕ) : List ℕ := keepTick^[3*v.headI+1] v
noncomputable def controlProgram : PolyProgram control :=
  (PolyProgram.safeIterate keepTickProgram 10 3 keepTick_safe).comp
    ((Expr.add (.mul (c 3) (r 0)) (c 1)).program.cons PolyProgram.id)

lemma outputStep_safe (v : List ℕ) :
    (outputStep v).length≤v.length+4 ∧ maximum (outputStep v)≤ maximum v+1 := by
  have hr (j : Fin 4) : (outRead j).eval v≤ maximum v := by
    change (v.drop _).headI≤_
    exact (head_le_maximum _).trans (maximum_drop v _)
  have h1 := reg_le_maximum v 1
  have h2 := reg_le_maximum v 2
  have h0 := hr 0
  have h3 := hr 1
  have ht := maximum_drop v 3
  simp only [outputStep]
  split_ifs
  · constructor <;> omega
  · simp only [List.cons_append,List.nil_append,List.length_cons,List.length_drop,maximum_cons]
    constructor
    · omega
    · exact max_le (by omega) (max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega))))

noncomputable def outputLoopProgram : PolyProgram (fun v=>outputStep^[v.headI] v.tail) :=
  PolyProgram.safeIterate outputStepProgram 4 1 outputStep_safe

def prepareOutput (v : List ℕ) : List ℕ :=
  [v.headI,(r 3).eval v,(r 5).eval v,0,2]++v.drop 6
noncomputable def prepareOutputProgram : PolyProgram prepareOutput :=
  PolyProgram.head.cons ((r 3).program.cons ((r 5).program.cons
    ((c 0).program.cons ((c 2).program.cons (PolyProgram.drop 6)))))

def universalRaw (v : List ℕ) : List ℕ :=
  let z := prepareOutput (control v)
  (outputStep^[z.headI] z.tail).drop 3

noncomputable def universalProgram : PolyProgram universalRaw :=
  (PolyProgram.drop 3).comp (outputLoopProgram.comp (prepareOutputProgram.comp controlProgram))

lemma universalRaw_spec {c v w B} (hr : Runs c v w B) (hl : w.length≤B) (base : Heap) :
    ∃h,universalRaw (B::(initialState c v base).encode)=w.reverse++2::words h := by
  obtain ⟨t,ht,hc⟩ := hr
  obtain ⟨h,out,ho,he⟩ := CodeRun.interpreted hc base ht
  refine ⟨h,?_⟩
  have hh : control (B::(initialState c v base).encode)=B::(State.mk 2 0 out 0 h).encode := by
    simpa only [control,List.headI_cons,keepTick_iter] using congrArg (List.cons B) he
  simp only [universalRaw,hh]
  have hp : prepareOutput (B::(State.mk 2 0 out 0 h).encode)=B::(OutputState.mk out h []).encode := rfl
  rw [hp]
  simp only [List.headI_cons,List.tail_cons]
  rw [ho.output_padded [] hl]
  simp only [List.append_nil,OutputState.encode,List.cons_append,List.nil_append]
  rfl

end MinUncut.Costed.Arena

end

end OAI
