import Mathlib
import OAI.Computability.DirectedFeedback.Games.EqualityFiber

namespace OAI

namespace DFVSGames.Theorem

theorem exists_binaryGapReduction (ε δ : ℝ)
    (hε : 0 < ε) (_hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (_hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  obtain ⟨P⟩ := ParameterSelection.exists_outerParameters ε δ hε hδ
  obtain ⟨M⟩ := Decoder.MatrixGap.exists_parameters P.pStar P.pStar_pos
  exact ⟨FromMatrixGap.reduction P M⟩

end DFVSGames.Theorem

namespace DFVSGames

theorem theorem11 (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) :=
  Theorem.exists_binaryGapReduction ε δ hε hεhalf hδ hδhalf

end DFVSGames

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
namespace Output

def subst {r s : Nat} (ρ : Fin r → Expr s) : Output r → Output s
  | .nil => .nil
  | .bit b => .bit b
  | .nat e => .nat (e.subst ρ)
  | .append a b => .append (subst ρ a) (subst ρ b)
  | .loop b e => .loop (b.subst ρ) (subst (Fin.cons (.arg 0) (fun i => (ρ i).rename Fin.succ)) e)
  | .when t b => .when (t.subst ρ) (subst ρ b)

theorem eval_subst {r s : Nat} (ρ : Fin r → Expr s) (e : Output r) (x : List Bool) (a : Fin s → Nat) :
    (e.subst ρ).eval x a = e.eval x (fun i => (ρ i).eval x a) := by
  induction e generalizing s with
  | nil => rfl
  | bit b => rfl
  | nat e => simp [subst,eval,Expr.eval_subst]
  | append a b iha ihb => simp [subst,eval,iha,ihb]
  | when t b ih => simp [subst,eval,ih,Expr.eval_subst]
  | loop b e ihe =>
    simp only [subst,eval,Expr.eval_subst,ihe]
    congr 1
    funext i
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Expr.eval]
    · simp [Expr.eval_rename,Function.comp_def]
end Output

def OutDef {r : Nat} (f : List Bool → (Fin r → Nat) → List Bool) : Prop :=
  ∃ e : Output r, ∀ x a, e.eval x a=f x a

namespace OutDef
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → List Bool}

theorem congr (hf : OutDef f) (h : ∀ x a, f x a=g x a) : OutDef g := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e,fun x a => (he x a).trans (h x a)⟩

theorem nil : OutDef (fun (_ : List Bool) (_ : Fin r → Nat) => []) := ⟨.nil,fun _ _ => rfl⟩
theorem bit (b : Bool) : OutDef (fun (_ : List Bool) (_ : Fin r → Nat) => [b]) := ⟨.bit b,fun _ _ => rfl⟩
theorem nat {f : List Bool → (Fin r → Nat) → Nat} (hf : Def f) :
    OutDef (fun x a => (List.replicate (f x a) true ++ [false])) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.nat e,by intro x a; simp only [Output.eval,he]⟩

theorem append (hf : OutDef f) (hg : OutDef g) : OutDef (fun x a => f x a++g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.append e d,by intro x a; simp only [Output.eval,he,hd]⟩

theorem const (bits : List Bool) : OutDef (fun (_ : List Bool) (_ : Fin r → Nat) => bits) := by
  induction bits with
  | nil => exact nil
  | cons b bs ih => simpa using (bit b).append ih

theorem subst {s : Nat} (hf : OutDef f) (ρ : Fin r → List Bool → (Fin s → Nat) → Nat)
    (hρ : ∀ i, Def (ρ i)) : OutDef (fun x a => f x (fun i => ρ i x a)) := by
  choose terms hterms using hρ
  obtain ⟨e,he⟩ := hf
  refine ⟨e.subst terms,?_⟩
  intro x a
  rw [Output.eval_subst]
  simpa only [hterms] using he x (fun i => ρ i x a)

theorem rename {s : Nat} (hf : OutDef f) (ρ : Fin r → Fin s) : OutDef (fun x a => f x (a ∘ ρ)) :=
  hf.subst (fun i _ a => a (ρ i)) (fun i => Def.arg (ρ i))

theorem loop {b : List Bool → (Fin r → Nat) → Nat}
    {e : List Bool → (Fin (r+1) → Nat) → List Bool} (hb : Def b) (he : OutDef e) :
    OutDef (fun x a => (List.range (b x a)).flatMap (fun i => e x (Fin.cons i a))) := by
  obtain ⟨b,hb⟩ := hb; obtain ⟨e,he⟩ := he
  exact ⟨.loop b e,by intro x a; simp only [Output.eval,hb,he]⟩

theorem when {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p) (hf : OutDef f) :
    OutDef (fun x a => if p x a then f x a else []) := by
  obtain ⟨t,ht⟩ := hp; obtain ⟨e,he⟩ := hf
  refine ⟨.when t e,?_⟩
  intro x a
  simp only [Output.eval,ht,he]
  by_cases h : p x a <;> simp [h]

theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p) (hf : OutDef f) (hg : OutDef g) :
    OutDef (fun x a => if p x a then f x a else g x a) := by
  apply ((hf.when hp).append (hg.when hp.not)).congr
  intro x a
  by_cases h : p x a <;> simp [h]

theorem flatMap {I : Type} (l : List I) (f : I → List Bool → (Fin r → Nat) → List Bool)
    (hf : ∀ i ∈ l, OutDef (f i)) : OutDef (fun x a => l.flatMap (fun i => f i x a)) := by
  induction l with
  | nil => exact nil
  | cons i l ih =>
    exact (hf i (by simp)).append (ih (fun j hj => hf j (by simp [hj])))

theorem finiteBind {I : Type} [Fintype I] {i : List Bool → (Fin r → Nat) → I}
    (hi : FDef i) (f : I → List Bool → (Fin r → Nat) → List Bool)
    (hf : ∀ j, OutDef (f j)) : OutDef (fun x a => f (i x a) x a) := by
  have hh := flatMap (Finset.univ.toList) (fun j x a => if i x a=j then f j x a else [])
    (fun j _ => (hf j).when (hi j))
  apply hh.congr
  intro x a
  have aux (l : List I) (hd : l.Nodup) (hm : i x a ∈ l) :
      l.flatMap (fun j => if i x a=j then f j x a else []) = f (i x a) x a := by
    induction l with
    | nil => simp at hm
    | cons j js ih =>
      rw [List.flatMap_cons]
      rcases List.nodup_cons.mp hd with ⟨hnot,hd⟩
      by_cases hj : i x a=j
      · subst j
        have hn : js.flatMap (fun j => if i x a=j then f j x a else []) = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro k hk
          simp [show i x a≠k from fun h => hnot (h ▸ hk)]
        simp [hn]
      · simp only [hj,ite_false,List.nil_append]
        exact ih hd (by simpa [hj] using hm)
  exact aux _ (Finset.nodup_toList _) (by simp)

end OutDef
end DirectedFeedback.BoundedExpr

end

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
open DFVSGames.Foundations DFVSGames.Foundations.PCP DFVSGames.Foundations.Complexity
namespace CNFPrinter

abbrev Lit := Nat × Bool

def literalBits (l : Lit) : List Bool := encodeWords [l.1,if l.2 then 1 else 0]
def clauseBits (a b c : Lit) : List Bool := literalBits a ++ literalBits b ++ literalBits c

def rawSplit : List Lit → List Nat → List Bool
  | [a,b,c], [] => clauseBits a b c
  | a::b::rest, y::ys => clauseBits a b (y,true) ++ rawSplit ((y,false)::rest) ys
  | _, _ => []

theorem rawSplit_eq {n : Nat} (ls : List (Target.Literal n)) (ys : List (Fin n)) :
    rawSplit (ls.map (fun l => (l.variableIndex.val,l.positive))) (ys.map Fin.val) =
      encodeWords ((VerifierToCNF.splitLong ls ys).flatMap clauseWords) := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_,_] => rfl
    | [a,b,c] =>
      cases ha : a.positive <;> cases hb : b.positive <;> cases hc : c.positive <;>
        simp [rawSplit,VerifierToCNF.splitLong,clauseBits,literalBits,clauseWords,literalWords,encodeWords,ha,hb,hc]
    | _::_::_::_::_ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a::b::rest =>
      simp only [List.map_cons,rawSplit,VerifierToCNF.splitLong,List.flatMap_cons,encodeWords_append]
      apply congrArg₂ List.append
      · cases ha : a.positive <;> cases hb : b.positive <;>
          simp [clauseBits,literalBits,clauseWords,literalWords,encodeWords,ha,hb]
      · simpa only [List.map_cons] using ih (⟨y,false⟩::rest)

theorem literalBits_def {r : Nat} {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (b : Bool) :
    OutDef (fun x a => literalBits (n x a,b)) := by
  apply ((OutDef.nat hn).append (OutDef.const (encodeWord (if b then 1 else 0)))).congr
  intro x a
  cases b <;> simp [literalBits,encodeWords,encodeWord]

theorem clauseBits_def {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}
    (hf : Def f) (hg : Def g) (hh : Def h) (a b c : Bool) :
    OutDef (fun x v => clauseBits (f x v,a) (g x v,b) (h x v,c)) :=
  ((literalBits_def hf a).append (literalBits_def hg b)).append (literalBits_def hh c)

theorem rawSplit_def {r : Nat}
    (ls : List ((List Bool → (Fin r → Nat) → Nat) × Bool))
    (ys : List (List Bool → (Fin r → Nat) → Nat))
    (hls : ∀ l ∈ ls, Def l.1) (hys : ∀ y ∈ ys, Def y) :
    OutDef (fun x a => rawSplit (ls.map (fun l => (l.1 x a,l.2))) (ys.map (fun y => y x a))) := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | [_,_] => exact OutDef.nil
    | [a,b,c] => exact clauseBits_def (hls a (by simp)) (hls b (by simp)) (hls c (by simp)) a.2 b.2 c.2
    | _::_::_::_::_ => exact OutDef.nil
  | cons y ys ih =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | a::b::rest =>
      have hy := hys y (by simp)
      have ht := ih ((y,false)::rest) (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hy
        · exact hls c (by simp [hc])) (fun z hz => hys z (by simp [hz]))
      simpa only [List.map_cons,rawSplit] using
        (clauseBits_def (hls a (by simp)) (hls b (by simp)) hy a.2 b.2 true).append ht

structure Family (q : Nat) where
  verifier : List Bool → VerifierToCNF.FiniteVerifier q
  variables_def : Def (r:=0) (fun x _ => (verifier x).«variables»)
  events_def : Def (r:=0) (fun x _ => (verifier x).events)
  query : Fin q → List Bool → Nat → Nat
  query_def : ∀ i, Def (r:=1) (fun x a => query i x (a 0))
  query_correct : ∀ x e i, query i x e.val = ((verifier x).query e i).val
  accepts : VerifierToCNF.Pattern q → List Bool → Nat → Bool
  accepts_def : ∀ p, FDef (r:=1) (fun x a => accepts p x (a 0))
  accepts_correct : ∀ x e p, accepts p x e.val = (verifier x).accepts e p

namespace Family
variable {q : Nat} (F : Family q) (hq : 3≤q)

def blockBits (x : List Bool) (e : Nat) (p : VerifierToCNF.PatternIndex q) : List Bool :=
  let bits := VerifierToCNF.patternAt q p
  if F.accepts bits x e then
    (List.replicate (q-2) (clauseBits (F.query ⟨0,by omega⟩ x e,true)
      (F.query ⟨0,by omega⟩ x e,false) (F.query ⟨0,by omega⟩ x e,true))).flatten
  else rawSplit
    ((List.ofFn (fun i => (F.query i x e,!(bits i)))))
    (List.ofFn (fun j : Fin (q-3) => (F.verifier x).«variables»+
      ((e*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)))

def eventBits (x : List Bool) (e : Nat) : List Bool :=
  (List.finRange (VerifierToCNF.patterns q).length).flatMap (F.blockBits hq x e)

def bits (x : List Bool) : List Bool :=
  encodeWords [(F.verifier x).«variables»+(F.verifier x).events*(VerifierToCNF.patterns q).length*(q-3),
    (F.verifier x).events*(2^q*(q-2))] ++
    (List.range (F.verifier x).events).flatMap (F.eventBits hq x)

theorem blockBits_def (p : VerifierToCNF.PatternIndex q) :
    OutDef (r:=1) (fun x a => F.blockBits hq x (a 0) p) := by
  have hv := F.variables_def.rename (Fin.elim0 : Fin 0 → Fin 1)
  have hf (j : Fin (q-3)) : Def (r:=1) (fun x a => (F.verifier x).«variables»+
      (((a 0)*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)) :=
    hv.add ((((Def.arg 0).mul (Def.lit _)).add (Def.lit _)).mul (Def.lit _) |>.add (Def.lit _))
  have hs := rawSplit_def
    (List.ofFn (fun i : Fin q => ((fun x (a : Fin 1 → Nat) => F.query i x (a 0)),
      !(VerifierToCNF.patternAt q p i))))
    (List.ofFn (fun j : Fin (q-3) => fun x (a : Fin 1 → Nat) => (F.verifier x).«variables»+
      (((a 0)*(VerifierToCNF.patterns q).length+p.val)*(q-3)+j.val)))
    (by intro l hl; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; exact F.query_def i)
    (by intro y hy; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hy; exact hf j)
  have ht := OutDef.flatMap (List.replicate (q-2) ())
    (fun _ x (a : Fin 1 → Nat) => clauseBits (F.query ⟨0,by omega⟩ x (a 0),true)
      (F.query ⟨0,by omega⟩ x (a 0),false) (F.query ⟨0,by omega⟩ x (a 0),true))
    (fun _ _ => clauseBits_def (F.query_def _) (F.query_def _) (F.query_def _) true false true)
  apply (OutDef.ite (F.accepts_def (VerifierToCNF.patternAt q p) |>.bool_true) ht hs).congr
  intro x a
  simp [blockBits,List.map_ofFn,List.flatMap_replicate,Function.comp_def]

theorem eventBits_def : OutDef (r:=1) (fun x a => F.eventBits hq x (a 0)) :=
  OutDef.flatMap _ (fun p x a => F.blockBits hq x (a 0) p) (fun p _ => F.blockBits_def hq p)

theorem bits_def : OutDef (r:=0) (fun x _ => F.bits hq x) := by
  have hvars := F.variables_def.add ((F.events_def.mul (Def.lit (VerifierToCNF.patterns q).length)).mul (Def.lit (q-3)))
  have hclauses := F.events_def.mul (Def.lit (2^q*(q-2)))
  apply (((OutDef.nat hvars).append (OutDef.nat hclauses)).append
    (OutDef.loop F.events_def (F.eventBits_def hq))).congr
  intro x a
  simp [bits,encodeWords,encodeWord]

end Family
end CNFPrinter
end DirectedFeedback.BoundedExpr

end

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr.CNFPrinter
open DFVSGames.Foundations DFVSGames.Foundations.PCP DFVSGames.Foundations.Complexity

theorem encodeWords_flatMap {I : Type} (l : List I) (f : I → List Nat) :
    encodeWords (l.flatMap f) = l.flatMap (fun i => encodeWords (f i)) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem map_finRange_val (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem range_flatMap {I : Type} {n : Nat} (f : Nat → List I) (g : Fin n → List I)
    (hg : ∀ i, f i.val=g i) : (List.range n).flatMap f=(List.finRange n).flatMap g := by
  rw [← map_finRange_val,List.flatMap_map]
  have he : (fun i : Fin n => f i.val)=g := funext hg
  rw [he]

namespace Family
variable {q : Nat} (F : Family q) (hq : 3≤q)

theorem blockBits_correct (x : List Bool) (e : Fin (F.verifier x).events)
    (p : VerifierToCNF.PatternIndex q) :
    F.blockBits hq x e.val p = encodeWords ((VerifierToCNF.block (F.verifier x) hq e p).flatMap clauseWords) := by
  unfold blockBits VerifierToCNF.block
  dsimp only
  rw [F.accepts_correct x e]
  split
  · have he : clauseBits (F.query ⟨0,by omega⟩ x e.val,true)
        (F.query ⟨0,by omega⟩ x e.val,false) (F.query ⟨0,by omega⟩ x e.val,true) =
        encodeWords (clauseWords (VerifierToCNF.tautology (F.verifier x) hq e)) := by
      simp [F.query_correct,clauseBits,literalBits,clauseWords,literalWords,
        VerifierToCNF.tautology,VerifierToCNF.oldIndex,encodeWords]
    rw [encodeWords_flatMap,List.flatMap_replicate,← he]
  · rw [← rawSplit_eq]
    apply congrArg₂ rawSplit
    · simp only [VerifierToCNF.forbiddenClause,List.map_ofFn]
      congr 1
      funext i
      simp [VerifierToCNF.liftLiteral,VerifierToCNF.forbiddenLiteral,VerifierToCNF.oldIndex,F.query_correct]
    · simp only [VerifierToCNF.auxiliaryNames,List.map_ofFn]
      congr 1
      funext j
      exact (VerifierToCNF.freshIndex_value _ _ _ _).symm

theorem eventBits_correct (x : List Bool) (e : Fin (F.verifier x).events) :
    F.eventBits hq x e.val = encodeWords ((VerifierToCNF.eventBlock (F.verifier x) hq e).flatMap clauseWords) := by
  simp only [eventBits,VerifierToCNF.eventBlock,List.flatMap_assoc,encodeWords_flatMap]
  congr 1
  funext p
  simpa only [encodeWords_flatMap] using F.blockBits_correct hq x e p

theorem bits_correct (x : List Bool) :
    F.bits hq x = formulaBits (VerifierToCNF.convert (F.verifier x) hq) := by
  unfold bits formulaBits formulaWords
  rw [encodeWords_append,VerifierToCNF.convert_clause_count]
  apply congrArg₂ List.append
  · rfl
  · change (List.range (F.verifier x).events).flatMap (F.eventBits hq x) =
      encodeWords (((List.finRange (F.verifier x).events).flatMap
        (VerifierToCNF.eventBlock (F.verifier x) hq)).flatMap clauseWords)
    rw [List.flatMap_assoc,encodeWords_flatMap]
    exact range_flatMap _ _ (F.eventBits_correct hq x)

noncomputable def computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    formulaBits (fun x => VerifierToCNF.convert (F.verifier x) hq) := by
  let o := Classical.choose (F.bits_def hq)
  have ho : ∀ x, o.eval x Fin.elim0 = formulaBits (VerifierToCNF.convert (F.verifier x) hq) := by
    intro x
    exact (Classical.choose_spec (F.bits_def hq) x Fin.elim0).trans (F.bits_correct hq x)
  exact Output.realizes _ _ o ho

theorem computation_finite (k : (F.computation hq).tm.K) : Finite ((F.computation hq).tm.Γ k) := by
  unfold computation
  exact Output.realizes_alphabet _ _ _ _ k

end Family
end DirectedFeedback.BoundedExpr.CNFPrinter

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr.UnaryRead
open DFVSGames.Foundations.Complexity

def zerosBefore (x : List Bool) (i : Nat) : Nat := (x.take i).count false

def word (x : List Bool) (j : Nat) : Nat :=
  ∑ i ∈ Finset.range x.length, if x[i]?=some true ∧ zerosBefore x i=j then 1 else 0

theorem count_eq_sum {A : Type} [DecidableEq A] (l : List A) (b : A) :
    l.count b = ∑ i ∈ Finset.range l.length, if l[i]?=some b then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq]
    rw [← ih]
    by_cases h : a=b <;> simp [h]

theorem zerosBefore_def {r : Nat} {i : List Bool → (Fin r → Nat) → Nat} (hi : Def i) :
    Def (fun x a => zerosBefore x (i x a)) := by
  have hb := (LDef.input (r:=r+1)).get (fun _ a => a 0) (Def.arg 0)
  apply ((hi.min Def.length).sum (hb (some false))).congr
  intro x a
  rw [zerosBefore,count_eq_sum,List.length_take]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < min (i x a) x.length := Finset.mem_range.mp hj
  simp [show j < i x a by omega]

theorem word_def {r : Nat} {j : List Bool → (Fin r → Nat) → Nat} (hj : Def j) :
    Def (fun x a => word x (j x a)) := by
  have hz := zerosBefore_def (r:=r+1) (Def.arg 0)
  have hb := (LDef.input (r:=r+1)).get (fun _ a => a 0) (Def.arg 0)
  have hp := PDef.and (hb (some true) : PDef (fun x a => x[a 0]?=some true))
    (PDef.nat_eq hz (hj.rename Fin.succ))
  apply (Def.length.sum hp).congr
  intro x a
  simp only [word,Function.comp_def,Fin.cons_zero,Fin.cons_succ]

@[simp] theorem word_nil (j : Nat) : word [] j=0 := by simp [word]

theorem word_true (x : List Bool) (j : Nat) :
    word (true::x) j = (if j=0 then 1 else 0)+word x j := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,zerosBefore,List.take_zero,
    List.count_nil,true_and,List.take_succ_cons]
  simp [eq_comm,word,zerosBefore,Nat.add_comm]

theorem word_false_zero (x : List Bool) : word (false::x) 0=0 := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp [zerosBefore]

theorem word_false_succ (x : List Bool) (j : Nat) : word (false::x) (j+1)=word x j := by
  rw [word,List.length_cons,Finset.sum_range_succ']
  simp only [zerosBefore,List.take_zero,List.count_nil,List.getElem?_cons_zero,
    Bool.false_eq_true,Option.some.injEq,false_and,↓reduceIte,
    List.getElem?_cons_succ,List.take_succ_cons,List.count_cons_self,Nat.add_right_cancel_iff]
  rfl

theorem word_prefix_zero (n : Nat) (x : List Bool) :
    word (List.replicate n true ++ false::x) 0=n := by
  induction n with
  | zero => simp [word_false_zero]
  | succ n ih => simp [List.replicate_succ,word_true,ih,Nat.add_comm]

theorem word_prefix_succ (n : Nat) (x : List Bool) (j : Nat) :
    word (List.replicate n true ++ false::x) (j+1)=word x j := by
  induction n with
  | zero => simp [word_false_succ]
  | succ n ih => simp [List.replicate_succ,word_true,ih]

theorem word_encoded (ns : List Nat) (j : Nat) : word (encodeWords ns) j=ns[j]?.getD 0 := by
  induction ns generalizing j with
  | nil => simp [encodeWords]
  | cons n ns ih =>
    cases j with
    | zero => simpa [encodeWords,encodeWord,List.append_assoc] using word_prefix_zero n (encodeWords ns)
    | succ j => simpa [encodeWords,encodeWord,List.append_assoc,ih] using word_prefix_succ n (encodeWords ns) j

end DirectedFeedback.BoundedExpr.UnaryRead

end

end OAI
