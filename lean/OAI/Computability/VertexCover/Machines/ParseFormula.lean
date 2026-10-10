import Mathlib
import OAI.Computability.VertexCover.Reduction.Soundness
import OAI.Computability.VertexCover.Machines.ParseSize

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine.FormulaParser
open UniqueGames.BinaryFormula UniqueGames.BinaryEncoding

abbrev Acc := List Clause × List Bool
abbrev accCode : Acc → List Bool := prodBits (listBits clauseCode) id
abbrev State := Bool × Option Acc
abbrev stateCode : State → List Bool := prodBits boolBits (optionBits accCode)

def oneStep (p : Acc) : State :=
  if p.2.isEmpty then (false,none)
  else if p.2.headD false then
    let parsed := parseClause p.2.tail
    (parsed.isSome,parsed.map (fun q => (q.1::p.1,q.2)))
  else (false,some (p.1,p.2.tail))

def step (s : State) : State := if s.1 then oneStep (s.2.getD ([],[])) else s

noncomputable def oneStepPoly : Poly accCode stateCode oneStep := by
  let out := Poly.fst (listBits clauseCode) id
  let bs := Poly.snd (listBits clauseCode) id
  let tail := bs.comp Poly.tail
  let parsed := tail.comp clausePoly
  let e := prodBits clauseCode id
  let cs := Poly.fst (listBits clauseCode) e
  let c := (Poly.snd (listBits clauseCode) e).comp (Poly.fst clauseCode id)
  let rest := (Poly.snd (listBits clauseCode) e).comp (Poly.snd clauseCode id)
  let collect := ((c.pair cs).comp (Poly.listCons clauseCode)).pair rest
  let data := (out.pair parsed).comp
    (Poly.optionMapWith (listBits clauseCode) e accCode (clauseDefault,[]) collect)
  let yes := (parsed.comp (Poly.isSome e)).pair data
  let no := (Poly.const accCode boolBits false).pair ((out.pair tail).comp (Poly.some accCode))
  let nonempty := (bs.comp (Poly.headD false)).ite yes no
  exact ((bs.comp Poly.isEmpty).ite (Poly.const accCode stateCode (false,none)) nonempty).congr (fun _ => rfl)

noncomputable def stepPoly : Poly stateCode stateCode step :=
  ((Poly.fst boolBits (optionBits accCode)).ite
    (((Poly.snd boolBits (optionBits accCode)).comp (Poly.getD accCode ([],[]))).comp oneStepPoly)
    (Poly.identity stateCode)).congr (fun _ => rfl)

def budget (s : State) : ℕ := match s.2 with
  | none => 10
  | some (out,bs) => 2*(listBits clauseCode out).length+32*bs.length+10

theorem size_le_budget (s : State) : (stateCode s).length ≤ budget s := by
  rcases s with ⟨b,v⟩
  cases v with
  | none => simp [stateCode,prodBits,pairBits_length,boolBits,optionBits,budget]
  | some p =>
    simp only [stateCode,prodBits,pairBits_length,boolBits,List.length_nil,
      optionBits,List.length_cons,accCode,id_eq,budget]
    omega

theorem budget_le_size (s : State) : budget s ≤ 32*((stateCode s).length+1) := by
  rcases s with ⟨b,v⟩
  cases v with
  | none => simp [stateCode,prodBits,pairBits_length,boolBits,optionBits,budget]
  | some p =>
    simp only [stateCode,prodBits,pairBits_length,boolBits,List.length_nil,
      optionBits,List.length_cons,accCode,id_eq,budget]
    omega

theorem step_budget (s : State) : budget (step s) ≤ budget s := by
  rcases s with ⟨b,v⟩
  cases b with
  | false => rfl
  | true =>
    cases v with
    | none => rfl
    | some p =>
      rcases p with ⟨out,bs⟩
      cases bs with
      | nil => simp [step,oneStep,budget]
      | cons b bs =>
        cases b with
        | false => simp [step,oneStep,budget,List.length_cons]
        | true =>
          cases h : parseClause bs with
          | none => simp [step,oneStep,budget,h]
          | some p =>
            rcases p with ⟨c,rest⟩
            have he := congrArg List.length (clause_sound bs c rest h)
            simp only [List.length_append] at he
            have hc := clause_code_bound c
            simp only [step,oneStep,ite_eq_left,Option.getD_some,List.isEmpty_cons,
              Bool.false_eq_true,ite_false,List.headD_cons,List.tail_cons,h,Option.isSome_some,
              Option.map_some,budget,listBits_cons_length,List.length_cons]
            omega

theorem run_budget (n : ℕ) (s : State) : budget (Iterate.run step n s) ≤ budget s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact (ih (step s)).trans (step_budget s)

noncomputable def runPoly : Poly (prodBits natBits stateCode) stateCode
    (fun p : ℕ × State => Iterate.run step p.1 p.2) :=
  Poly.iterate stateCode stepPoly (100*(Polynomial.X+1)) (by
    intro n s k l h
    have hs := (size_le_budget (Iterate.run step k s)).trans (run_budget k s)
    have hb := budget_le_size s
    simp only [prodBits,pairBits_length,natBits_length,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at hs hb ⊢
    omega)

def observe (s : State) : Option Acc := if s.1 then none else s.2

theorem run_done (n : ℕ) (v : Option Acc) : Iterate.run step n (false,v)=(false,v) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem observe_run (fuel : ℕ) (out : List Clause) (input : List Bool) :
    observe (Iterate.run step fuel (true,some (out,input))) =
      (parseClauses fuel input).map (fun p => (p.1.reverse++out,p.2)) := by
  induction fuel generalizing out input with
  | zero => rfl
  | succ fuel ih =>
    cases input with
    | nil => simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_nil,
        ite_eq_left,run_done,observe,Bool.false_eq_true,ite_false,parseClauses,Option.map_none]
    | cons b bs =>
      cases b with
      | false =>
        simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_cons,
          Bool.false_eq_true,ite_eq_left,ite_false,List.headD_cons,List.tail_cons,run_done,observe,
          parseClauses,Option.map_some,List.reverse_nil,List.nil_append]
      | true =>
        cases h : parseClause bs with
        | none =>
          simp only [Iterate.run,step,oneStep,Option.getD_some,List.isEmpty_cons,
            Bool.false_eq_true,ite_eq_left,ite_false,List.headD_cons,List.tail_cons,h,Option.isSome_none,
            Option.map_none,run_done,observe,parseClauses,Option.bind_eq_bind,Option.bind_none]
        | some p =>
          rcases p with ⟨c,rest⟩
          have hstep : step (true,some (out,true::bs)) = (true,some (c::out,rest)) := by
            simp [step,oneStep,h]
          rw [Iterate.run,hstep,ih]
          simp only [parseClauses,h,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
          cases hp : parseClauses fuel rest <;>
            simp [List.reverse_cons,List.append_assoc]

noncomputable def observePoly : Poly stateCode (optionBits accCode) observe :=
  ((Poly.fst boolBits (optionBits accCode)).ite
    (Poly.const stateCode (optionBits accCode) none) (Poly.snd boolBits (optionBits accCode))).congr (fun _ => rfl)

noncomputable def clausesPoly : Poly (prodBits natBits id) (optionBits accCode)
    (fun p : ℕ × List Bool => parseClauses p.1 p.2) := by
  let e := prodBits natBits id
  let clock := Poly.fst natBits id
  let empty := Poly.const e (listBits clauseCode) []
  let initial := (Poly.const e boolBits true).pair
    (((empty.pair (Poly.snd natBits id)).comp (Poly.some accCode)))
  let running := ((clock.pair initial).comp runPoly).comp observePoly
  let reverse := ((Poly.fst (listBits clauseCode) id).comp
    (Poly.listReverse clauseCode clauseDefault)).pair (Poly.snd (listBits clauseCode) id)
  let c := running.comp (Poly.optionMap accCode accCode ([],[]) reverse)
  refine c.congr ?_
  intro ⟨n,bs⟩
  change (observe (Iterate.run step n (true,some ([],bs)))).map
    (fun p => (p.1.reverse,p.2)) = parseClauses n bs
  rw [observe_run]
  cases h : parseClauses n bs <;> simp

noncomputable def decodePoly : Poly id (optionBits formulaCode) decodeFormula := by
  let parser := ((rawLength.comp Poly.natSucc).pair (Poly.identity id)).comp clausesPoly
  let done := (Poly.snd (listBits clauseCode) id).comp Poly.isEmpty
  let form : Poly accCode formulaCode (fun p : Acc => ⟨p.1⟩) :=
    (Poly.fst (listBits clauseCode) id).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  let finish := done.ite (form.comp (Poly.some formulaCode))
    (Poly.const accCode (optionBits formulaCode) none)
  exact (parser.comp (Poly.optionBind accCode formulaCode ([],[]) finish)).congr (fun bs => by
    change ((parseClauses (bs.length+1) bs).bind (fun a =>
      if a.2.isEmpty then some (⟨a.1⟩ : Formula) else none)) = decodeFormula bs
    cases h : parseClauses (bs.length+1) bs with
    | none => simp [decodeFormula,h]
    | some p => rcases p with ⟨cs,rest⟩; cases rest <;> simp [decodeFormula,h])

noncomputable def inputFormulaPoly : Poly id formulaCode VertexCover.ClauseProjection.inputFormula :=
  decodePoly.comp (Poly.getD formulaCode VertexCover.ClauseProjection.falseFormula)

end VertexCover.Machine.FormulaParser
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
