import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.FiniteScan

namespace OAI

namespace LargeIndependentSets.BinarySyntax

inductive Phase where
  | headerMark | headerPayload
  | widthStart | widthBit0
  | widthMark1 (b : Bool) | widthBit1 (b : Bool)
  | widthMark2 (b c : Bool)
  | sign (remaining : Fin 3) (first : Bool)
  | mark (remaining : Fin 3)
  | payload (remaining : Fin 3)
  | bad
  deriving DecidableEq, Fintype

def after (r : Fin 3) : Phase :=
  if h : r.val=0 then .widthStart else .sign ⟨r.val-1,by omega⟩ false

def width (n : Fin 4) : Phase :=
  if h : n.val=0 then .widthStart else .sign ⟨n.val-1,by omega⟩ true

def transition : Phase → Bool → Phase
  | .headerMark, true => .headerPayload
  | .headerMark, false => .widthStart
  | .headerPayload, _ => .headerMark
  | .widthStart, true => .widthBit0
  | .widthStart, false => .widthStart
  | .widthBit0, b => .widthMark1 b
  | .widthMark1 b, true => .widthBit1 b
  | .widthMark1 b, false => if b then .sign 0 true else .widthStart
  | .widthBit1 b, c => .widthMark2 b c
  | .widthMark2 b c, false => if c then .sign (if b then 2 else 1) true
      else if b then .sign 0 true else .widthStart
  | .widthMark2 _ _, true => .bad
  | .sign r _, _ => .mark r
  | .mark r, true => .payload r
  | .mark r, false => after r
  | .payload r, _ => .mark r
  | .bad, _ => .bad

def run (q : Phase) (s : List Bool) : Phase := s.foldl transition q

@[simp] lemma run_nil (q : Phase) : run q [] = q := rfl
@[simp] lemma run_cons (q : Phase) (b : Bool) (s : List Bool) :
    run q (b::s) = run (transition q b) s := rfl
lemma run_append (q : Phase) (a b : List Bool) : run q (a++b) = run (run q a) b :=
  List.foldl_append

lemma run_header (s : List Bool) : run .headerMark (frame s) = .widthStart := by
  induction s with
  | nil => rfl
  | cons b bs ih => simpa only [frame,run_cons,transition] using ih

lemma run_name (r : Fin 3) (s : List Bool) : run (.mark r) (frame s) = after r := by
  induction s with
  | nil => rfl
  | cons b bs ih => simpa only [frame,run_cons,transition] using ih

lemma run_literal (r : Fin 3) (first : Bool) (l : Literal) :
    run (.sign r first) (literalBits l) = after r := by
  simpa only [literalBits,nameBits,run_cons,transition] using run_name r l.name.bits

lemma run_width (n : Fin 4) : run .widthStart (nameBits n.val) = width n := by
  fin_cases n <;> rfl

lemma run_clause (C : List Literal) (hw : C.length ≤ 3) :
    run .widthStart (clauseBits C) = .widthStart := by
  unfold clauseBits
  rw [run_append,run_width ⟨C.length,by omega⟩]
  cases C with
  | nil => rfl
  | cons a C =>
    cases C with
    | nil =>
        change run (.sign 0 true) (literalBits a ++ []) = .widthStart
        simpa [after] using run_literal 0 true a
    | cons b C =>
      cases C with
      | nil =>
        simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
          List.append_nil]
        change run (.sign 1 true) (literalBits a ++ literalBits b) = _
        rw [run_append,run_literal]
        exact run_literal 0 false b
      | cons c C =>
        have hc : C=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hw
          omega
        subst C
        simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
          List.append_nil]
        change run (.sign 2 true) (literalBits a ++ (literalBits b ++ literalBits c)) = _
        rw [run_append,run_literal]
        change run (.sign 1 false) (literalBits b ++ literalBits c) = _
        rw [run_append,run_literal]
        exact run_literal 0 false c

lemma run_clauses (Cs : List (List Literal)) (hw : ∀ C ∈ Cs, C.length ≤ 3) :
    run .widthStart (Cs.flatMap clauseBits) = .widthStart := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
    rw [List.flatMap_cons,run_append,run_clause C (hw C (by simp))]
    exact ih (fun D hD => hw D (by simp [hD]))

lemma run_formula (F : Formula) : run .headerMark (formulaBits F) = .widthStart := by
  rw [formulaBits,run_append]
  simp only [nameBits,run_header]
  exact run_clauses F.clauses F.width

noncomputable def phaseEquiv : Phase ≃ Fin (Fintype.card Phase) := Fintype.equivFin Phase
noncomputable def finiteTransition (q : Fin (Fintype.card Phase)) (b : Bool) :=
  phaseEquiv (transition (phaseEquiv.symm q) b)

lemma finite_run (q : Phase) (s : List Bool) :
    s.foldl finiteTransition (phaseEquiv q) = phaseEquiv (run q s) := by
  induction s generalizing q with
  | nil => rfl
  | cons b s ih => simpa [List.foldl_cons,finiteTransition,run,transition] using ih (transition q b)

noncomputable def annotated (s : List Bool) :=
  FiniteScan.output finiteTransition (phaseEquiv .headerMark) s

lemma annotated_history (s : List Bool) (j : ℕ) (hj : j ≤ s.length) :
    (annotated s).history j = phaseEquiv (run .headerMark (s.take j)) := by
  rw [annotated,FiniteScan.output_history _ _ _ j hj,finite_run]

noncomputable def certificate : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) FiniteScan.State.bits annotated :=
  FiniteScan.certificate finiteTransition (phaseEquiv .headerMark)

lemma finiteAlphabet : IndependentSetsGames.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet
    certificate.tm := FiniteScan.finiteAlphabet _ _

end LargeIndependentSets.BinarySyntax

end OAI
