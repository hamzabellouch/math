import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.BinaryEvents
import OAI.Combinatorics.IndependentSets.Encoding.BinaryNameTables

namespace OAI

namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations

abbrev varCount (s : List Bool) : ℕ := s.length+1

def dense (s : List Bool) (p : ℕ) : Target.Literal (varCount s) :=
  ⟨⟨key s p,Nat.lt_succ_of_le (key_le s p)⟩,raw s p⟩

def constant (s : List Bool) (b : Bool) : Target.Literal (varCount s) := ⟨0,b⟩

def triple {n : ℕ} (a b c : Target.Literal n) : Target.Clause n := ⟨#[a,b,c],rfl⟩

def tautology (s : List Bool) : Target.Clause (varCount s) :=
  triple (constant s true) (constant s false) (constant s true)

def unitClause (s : List Bool) (b : Bool) : Target.Clause (varCount s) :=
  triple (constant s b) (constant s b) (constant s b)

def sourceClause (s : List Bool) (p : ℕ) (r : Fin 3) : Target.Clause (varCount s) :=
  triple (dense s p) (dense s (if 1 ≤ r.val then next s p else p))
    (dense s (if 2 ≤ r.val then next s (next s p) else p))

def eventAt (s : List Bool) (p : ℕ) : Option Mark :=
  event (run .headerMark (s.take p)) (raw s p)

def row (s : List Bool) (p : ℕ) (side : Bool) : Target.Clause (varCount s) :=
  match eventAt s p with
  | none => tautology s
  | some .empty => unitClause s side
  | some (.first r) => if side then tautology s else sourceClause s p r

def normalize (s : List Bool) : Target.Formula :=
  ⟨varCount s,(List.range s.length).flatMap (fun p => [row s p false,row s p true])⟩

@[simp] lemma literal_eval_iff {n : ℕ} (l : Target.Literal n) (σ : Fin n → Bool) :
    l.eval σ = true ↔ σ l.variableIndex = l.positive := by
  cases h : l.positive <;> simp [Target.Literal.eval,h]

@[simp] lemma triple_eval {n : ℕ} (a b c : Target.Literal n) (σ : Fin n → Bool) :
    (triple a b c).eval σ = true ↔ a.eval σ = true ∨ b.eval σ = true ∨ c.eval σ = true := by
  simp [triple,Target.Clause.eval,or_assoc]

lemma foldr_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => simp [Nat.bits_append_bit n b h,ih]

@[simp] lemma tautology_eval (s : List Bool) (σ : Fin (varCount s) → Bool) :
    (tautology s).eval σ = true := by
  simp [tautology,constant]

@[simp] lemma unitClause_eval (s : List Bool) (b : Bool) (σ : Fin (varCount s) → Bool) :
    (unitClause s b).eval σ = true ↔ σ 0 = b := by
  simp [unitClause,constant]

lemma eventAt_iff (s : List Bool) (p : ℕ) (hp : p<s.length) (e : Mark) :
    eventAt s p = some e ↔ (p,e) ∈ events .headerMark s := by
  simpa [eventAt,raw,List.getElem?_eq_getElem hp] using
    (events_complete .headerMark s p hp e).symm

def Realizes (s : List Bool) (σ : Fin (varCount s) → Bool) (θ : ℕ → Bool) : Prop :=
  ∀ pre l post, s=pre++literalBits l++post →
    σ ⟨key s pre.length,Nat.lt_succ_of_le (key_le s pre.length)⟩ = θ l.name

lemma raw_literal (pre post : List Bool) (l : Literal) :
    raw (pre++literalBits l++post) pre.length = l.positive := by
  rw [show pre.length=pre.length+0 by omega,raw_middle _ _ _ 0 (by simp [literalBits])]
  rfl

lemma dense_eval_iff {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (l : Literal)
    (hs : s=pre++literalBits l++post) :
    (dense s pre.length).eval σ = true ↔ θ l.name=l.positive := by
  rw [literal_eval_iff]
  change σ ⟨key s pre.length,_⟩ = raw s pre.length ↔ _
  rw [h pre l post hs,hs,raw_literal]

lemma exists_realizes_forward (s : List Bool) (θ : ℕ → Bool) :
    ∃ σ, Realizes s σ θ := by
  refine ⟨fun x => θ ((payload s x.val).foldr Nat.bit 0),?_⟩
  intro pre l post hs
  have hp : pre.length ≤ s.length := by simp only [hs,List.length_append]; omega
  change θ ((payload s (key s pre.length)).foldr Nat.bit 0)=θ l.name
  rw [key_payload s pre.length hp,hs,payload_literal,foldr_bits]

lemma exists_realizes_backward (s : List Bool) (σ : Fin (varCount s) → Bool) :
    ∃ θ, Realizes s σ θ := by
  classical
  let occurs (v : ℕ) := ∃ p, p ≤ s.length ∧ payload s p=v.bits
  let pos (v : ℕ) (h : occurs v) : ℕ := Classical.choose h
  let θ : ℕ → Bool := fun v => if h : occurs v then
    σ ⟨key s (pos v h),Nat.lt_succ_of_le (key_le s _)⟩ else false
  refine ⟨θ,?_⟩
  intro pre l post hs
  have hp : pre.length ≤ s.length := by simp only [hs,List.length_append]; omega
  have hv : payload s pre.length=l.name.bits := by rw [hs,payload_literal]
  have ho : occurs l.name := ⟨pre.length,hp,hv⟩
  dsimp only [θ]
  rw [dite_eq_left ho]
  have hpos := Classical.choose_spec ho
  have hkey : key s pre.length=key s (pos l.name ho) :=
    key_eq s _ _ hp hpos.1 (hv.trans hpos.2.symm)
  congr 1
  exact Fin.ext hkey

lemma sourceClause_one {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a : Literal)
    (hs : s=pre++literalBits a++post) :
    (sourceClause s pre.length 0).eval σ=true ↔ θ a.name=a.positive := by
  simp only [sourceClause,Fin.val_zero,show ¬1≤0 by omega,show ¬2≤0 by omega,ite_false,
    triple_eval,or_self]
  exact dense_eval_iff h pre post a hs

lemma sourceClause_two {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a b : Literal)
    (hs : s=pre++literalBits a++literalBits b++post) :
    (sourceClause s pre.length 1).eval σ=true ↔
      θ a.name=a.positive ∨ θ b.name=b.positive := by
  have ha : s=pre++literalBits a++(literalBits b++post) := by simpa [List.append_assoc] using hs
  have hb : s=(pre++literalBits a)++literalBits b++post := hs
  have hn : next s pre.length=(pre++literalBits a).length := by rw [ha,next_literal]
  simp only [sourceClause,show (1 : Fin 3).val=1 from rfl,le_refl,show ¬2≤1 by omega,
    ite_true,ite_false,triple_eval,hn,dense_eval_iff h pre _ a ha,
    dense_eval_iff h _ post b hb]
  tauto

lemma sourceClause_three {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a b c : Literal)
    (hs : s=pre++literalBits a++literalBits b++literalBits c++post) :
    (sourceClause s pre.length 2).eval σ=true ↔
      θ a.name=a.positive ∨ θ b.name=b.positive ∨ θ c.name=c.positive := by
  have ha : s=pre++literalBits a++(literalBits b++literalBits c++post) := by
    simpa [List.append_assoc] using hs
  have hb : s=(pre++literalBits a)++literalBits b++(literalBits c++post) := by
    simpa [List.append_assoc] using hs
  have hc : s=(pre++literalBits a++literalBits b)++literalBits c++post := hs
  have hn : next s pre.length=(pre++literalBits a).length := by rw [ha,next_literal]
  have hn' : next s (pre++literalBits a).length=(pre++literalBits a++literalBits b).length := by
    rw [hb,next_literal]
  simp only [sourceClause,show (2 : Fin 3).val=2 from rfl,show 1≤2 by omega,le_refl,ite_true,
    triple_eval,hn,hn',dense_eval_iff h pre _ a ha,dense_eval_iff h _ _ b hb,
    dense_eval_iff h _ post c hc]

def PairSatisfied (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool) : Prop :=
  (row s p false).eval σ=true ∧ (row s p true).eval σ=true

lemma pair_first (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool) (r : Fin 3)
    (he : eventAt s p=some (.first r)) :
    PairSatisfied s p σ ↔ (sourceClause s p r).eval σ=true := by
  simp [PairSatisfied,row,he]

lemma pair_empty (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool)
    (he : eventAt s p=some .empty) : ¬ PairSatisfied s p σ := by
  simp [PairSatisfied,row,he]

lemma pair_none (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool)
    (he : eventAt s p=none) : PairSatisfied s p σ := by
  simp [PairSatisfied,row,he]

lemma atClause {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (C : List Literal) (hw : C.length ≤ 3)
    (hs : s=pre++clauseBits C++post)
    (he : eventAt s (pre.length+(clauseMark C).1)=some (clauseMark C).2) :
    PairSatisfied s (pre.length+(clauseMark C).1) σ ↔
      ∃ l ∈ C, θ l.name=l.positive := by
  cases C with
  | nil =>
    have hn := pair_empty s _ σ he
    simp only [List.not_mem_nil,false_and,exists_false,iff_false]
    exact hn
  | cons a C =>
    cases C with
    | nil =>
      have hp : pre.length+(clauseMark [a]).1=(pre++nameBits 1).length := by
        simp [clauseMark]
      have he' : eventAt s (pre.length+(clauseMark [a]).1)=some (.first 0) := he
      rw [pair_first _ _ _ _ he',hp]
      have hs' : s=(pre++nameBits 1)++literalBits a++post := by
        simpa [clauseBits,List.append_assoc] using hs
      simpa using sourceClause_one h (pre++nameBits 1) post a hs'
    | cons b C =>
      cases C with
      | nil =>
        have hp : pre.length+(clauseMark [a,b]).1=(pre++nameBits 2).length := by
          simp [clauseMark]
        have he' : eventAt s (pre.length+(clauseMark [a,b]).1)=some (.first 1) := he
        rw [pair_first _ _ _ _ he',hp]
        have hs' : s=(pre++nameBits 2)++literalBits a++literalBits b++post := by
          simpa [clauseBits,List.append_assoc] using hs
        simpa [List.mem_cons,or_and_right,exists_or] using
          sourceClause_two h (pre++nameBits 2) post a b hs'
      | cons c C =>
        have hc : C=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hw
          omega
        subst C
        have hp : pre.length+(clauseMark [a,b,c]).1=(pre++nameBits 3).length := by
          simp [clauseMark]
        have he' : eventAt s (pre.length+(clauseMark [a,b,c]).1)=some (.first 2) := he
        rw [pair_first _ _ _ _ he',hp]
        have hs' : s=(pre++nameBits 3)++literalBits a++literalBits b++literalBits c++post := by
          simpa [clauseBits,List.append_assoc] using hs
        simpa [List.mem_cons,or_and_right,exists_or,or_assoc] using
          sourceClause_three h (pre++nameBits 3) post a b c hs'

lemma pairs_iff (s : List Bool) (σ : Fin (varCount s) → Bool) :
    (∀ C ∈ (normalize s).clauses, C.eval σ=true) ↔
      ∀ p<s.length, PairSatisfied s p σ := by
  change (∀ C ∈ (List.range s.length).flatMap (fun p => [row s p false,row s p true]),
    C.eval σ=true) ↔ _
  constructor
  · intro h p hp
    have hm (b : Bool) : row s p b ∈ (normalize s).clauses := by
      apply List.mem_flatMap.mpr
      refine ⟨p,List.mem_range.mpr hp,?_⟩
      cases b <;> simp
    exact ⟨h _ (hm false),h _ (hm true)⟩
  · intro h C hC
    obtain ⟨p,hp,hC⟩ := List.mem_flatMap.mp hC
    have hh := h p (List.mem_range.mp hp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl
    · exact hh.1
    · exact hh.2

lemma formula_atClause (F : Formula) {σ : Fin (varCount (formulaBits F)) → Bool}
    {θ : ℕ → Bool} (h : Realizes (formulaBits F) σ θ)
    (pre : List (List Literal)) (C : List Literal) (post : List (List Literal))
    (hF : F.clauses=pre++C::post) :
    let p := (nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1
    p < (formulaBits F).length ∧
      (PairSatisfied (formulaBits F) p σ ↔ ∃ l ∈ C, θ l.name=l.positive) := by
  dsimp only
  have hm := formula_clause_event F pre C post hF
  have hp := events_bound .headerMark (formulaBits F) _ _ hm
  refine ⟨hp,?_⟩
  have he := (eventAt_iff _ _ hp _).mpr hm
  have hh : F.clauses.length=(pre++C::post).length := congrArg List.length hF
  have hs : formulaBits F=(nameBits F.clauses.length++pre.flatMap clauseBits)++
      clauseBits C++post.flatMap clauseBits := by
    simp only [formulaBits,hF,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hc : C ∈ F.clauses := by rw [hF]; simp
  simpa only [List.length_append] using atClause h
    (nameBits F.clauses.length++pre.flatMap clauseBits) (post.flatMap clauseBits) C
    (F.width C hc) hs (by simpa only [List.length_append] using he)

theorem satisfiable_iff (F : Formula) :
    (normalize (formulaBits F)).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨σ,hσ⟩
    obtain ⟨θ,hθ⟩ := exists_realizes_backward (formulaBits F) σ
    refine ⟨θ,?_⟩
    intro C hC
    obtain ⟨pre,post,hF⟩ := List.mem_iff_append.mp hC
    have hp := formula_atClause F hθ pre C post hF
    exact hp.2.mp ((pairs_iff _ σ).mp hσ _ hp.1)
  · rintro ⟨θ,hθ⟩
    obtain ⟨σ,hσ⟩ := exists_realizes_forward (formulaBits F) θ
    refine ⟨σ,(pairs_iff _ σ).mpr ?_⟩
    intro p hp
    cases he : eventAt (formulaBits F) p with
    | none => exact pair_none _ _ _ he
    | some e =>
      obtain ⟨pre,C,post,hF,hp',he'⟩ := event_formula_location F p e
        ((eventAt_iff _ _ hp _).mp he)
      rw [hp']
      exact (formula_atClause F hσ pre C post hF).2.mpr
        (hθ C (by rw [hF]; simp))

end LargeIndependentSets.BinaryNormalize

end OAI
