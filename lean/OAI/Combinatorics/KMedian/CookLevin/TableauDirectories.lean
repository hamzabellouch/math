import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookSize
import OAI.Combinatorics.KMedian.Machines.OrderedLists
import OAI.Combinatorics.KMedian.Machines.TableBuilders
import OAI.Combinatorics.KMedian.Process.RoundingListOperations

namespace OAI

section Inline_PCPTableauDirectories
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau
open scoped Classical

variable {K : Type} (k0 : K)
abbrev VC := Fin 3 × (ℕ × (K × ℕ))
abbrev TC := Fin 9 × (ℕ × (K × ℕ))
def varCode {T L : ℕ} : Var (K := K) T L → VC (K := K)
  | .inl t => (0,t.val,k0,0)
  | .inr (.inl t) => (1,t.val,k0,0)
  | .inr (.inr (t,k,i)) => (2,t.val,k,i.val)
def clauseCode {T L : ℕ} : Clause (K := K) T L → TC (K := K)
  | .shape t k i => (0,t.val,k,i.val)
  | .end t k => (1,t.val,k,0)
  | .prefix t => (2,t.val,k0,0)
  | .control t => (3,t.val,k0,0)
  | .update t k i => (4,t.val,k,i.val)
def boundaryCode {L : ℕ} (b : BoundaryClause (K := K) L) : TC (K := K) :=
  match b.2 with
  | .inl _ => (if b.1 then 6 else 5,0,k0,0)
  | .inr (k,i) => (if b.1 then 8 else 7,0,k,i.val)
def testCode {T L : ℕ} : Clause (K := K) T L ⊕ BoundaryClause (K := K) L → TC (K := K) :=
  Sum.elim (clauseCode k0) (boundaryCode k0)
lemma varCode_injective (T L : ℕ) : Function.Injective (varCode k0 (T := T) (L := L)) := by
  rintro (a|a) (b|b) hab
  · exact congrArg Sum.inl (Fin.ext (congrArg (fun z => z.2.1) hab))
  · rcases b with b|⟨b,k,i⟩ <;> cases congrArg (fun z => z.1.val) hab
  · rcases a with a|⟨a,k,i⟩ <;> cases congrArg (fun z => z.1.val) hab
  · rcases a with a|⟨a,k,i⟩ <;> rcases b with b|⟨b,l,j⟩
    · exact congrArg (fun t => Sum.inr (Sum.inl t)) (Fin.ext (congrArg (fun z => z.2.1) hab))
    · cases congrArg (fun z => z.1.val) hab
    · cases congrArg (fun z => z.1.val) hab
    · have ht : a=b := Fin.ext (congrArg (fun z => z.2.1) hab)
      have hk : k=l := congrArg (fun z => z.2.2.1) hab
      have hi : i=j := Fin.ext (congrArg (fun z => z.2.2.2) hab)
      subst b; subst l; subst j; rfl
lemma clauseCode_injective (T L : ℕ) : Function.Injective (clauseCode k0 (T := T) (L := L)) := by
  intro a b hab
  cases a <;> cases b <;>
    simp only [clauseCode,Prod.mk.injEq] at hab <;>
    try { have h := congrArg Fin.val hab.1; contradiction }
  all_goals congr <;> first | exact Fin.ext hab.2.1 | exact hab.2.2.1 | exact Fin.ext hab.2.2.2
lemma boundaryCode_injective (L : ℕ) : Function.Injective (boundaryCode k0 (L := L)) := by
  rintro ⟨side,a⟩ ⟨side',b⟩ hab
  cases side <;> cases side' <;> rcases a with a|⟨k,i⟩ <;> rcases b with b|⟨l,j⟩ <;>
    simp only [boundaryCode,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at hab
  all_goals try { have h := congrArg Fin.val hab.1; contradiction }
  all_goals try { cases a; cases b; rfl }
  all_goals
    have hk := hab.2.2.1
    have hi := Fin.ext hab.2.2.2
    cases hk
    cases hi
    rfl
lemma testCode_injective (T L : ℕ) : Function.Injective (testCode k0 (T := T) (L := L)) := by
  rintro (a|a) (b|b) hab
  · exact congrArg Sum.inl (clauseCode_injective k0 T L hab)
  · cases a <;> rcases b with ⟨side,b⟩ <;> cases side <;> rcases b with b|⟨k,i⟩ <;>
      cases congrArg (fun z => z.1.val) hab
  · cases b <;> rcases a with ⟨side,a⟩ <;> cases side <;> rcases a with a|⟨k,i⟩ <;>
      cases congrArg (fun z => z.1.val) hab
  · exact congrArg Sum.inr (boundaryCode_injective k0 L hab)
variable [Fintype K]
noncomputable def varOrder (T L : ℕ) : Ordered (Var (K := K) T L) :=
  (Ordered.fin (T+1)).sum ((Ordered.fin T).sum ((Ordered.fin (T+1)).prod ((Ordered.fixed K).prod (Ordered.fin (L+1)))))
noncomputable def clauseOrder (T L : ℕ) : Ordered (Clause (K := K) T L) :=
  (((Ordered.fin (T+1)).prod ((Ordered.fixed K).prod (Ordered.fin L))).sum
    (((Ordered.fin (T+1)).prod (Ordered.fixed K)).sum
      ((Ordered.fin T).sum ((Ordered.fin T).sum
        ((Ordered.fin T).prod ((Ordered.fixed K).prod (Ordered.fin (L+1)))))))).map (Tableau.clauseEquiv T L).symm
noncomputable def boolOrder : Ordered Bool where
  entries := [false,true]
  nodup := by simp
  all b := by cases b <;> simp
noncomputable def boundaryOrder (L : ℕ) : Ordered (BoundaryClause (K := K) L) :=
  boolOrder.prod ((Ordered.fixed Unit).sum ((Ordered.fixed K).prod (Ordered.fin (L+1))))
noncomputable def testOrder (T L : ℕ) := (clauseOrder (K := K) T L).sum (boundaryOrder (K := K) L)
noncomputable def vars (T L : ℕ) : List (VC (K := K)) :=
  (List.range (T+1)).map (fun t => (0,t,k0,0)) ++
  (List.range T).map (fun t => (1,t,k0,0)) ++
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range (L+1)).map (fun i => (2,t,k,i))))
noncomputable def clauses (T L : ℕ) : List (TC (K := K)) :=
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range L).map (fun i => (0,t,k,i)))) ++
  (List.range (T+1)).flatMap (fun t => (Ordered.fixed K).entries.map (fun k => (1,t,k,0))) ++
  (List.range T).map (fun t => (2,t,k0,0)) ++
  (List.range T).map (fun t => (3,t,k0,0)) ++
  (List.range T).flatMap (fun t => (Ordered.fixed K).entries.flatMap
    (fun k => (List.range (L+1)).map (fun i => (4,t,k,i))))
noncomputable def boundaries (L : ℕ) : List (TC (K := K)) :=
  [false,true].flatMap (fun b => [(if b then 6 else 5,0,k0,0)] ++
    (Ordered.fixed K).entries.flatMap (fun k => (List.range (L+1)).map (fun i => (if b then 8 else 7,0,k,i))))
noncomputable def tests (T L : ℕ) : List (TC (K := K)) := clauses k0 T L++boundaries k0 L
lemma map_finRange {A : Type} (n : ℕ) (f : ℕ→A) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intros; simp
lemma flatMap_finRange {A : Type} (n : ℕ) (f : ℕ→List A) :
    (List.finRange n).flatMap (fun i => f i.val)=(List.range n).flatMap f := by
  rw [RoundingList.range_finRange,List.flatMap_map]
lemma vars_correct (T L : ℕ) : vars k0 T L=(varOrder (K := K) T L).entries.map (varCode k0) := by
  simp only [varOrder,Ordered.sum,Ordered.prod,Ordered.fin,List.map_append,List.map_map,
    List.product,List.map_flatMap,Function.comp_def,varCode]
  simp only [vars,RoundingList.range_finRange,List.flatMap_map,List.map_map,Function.comp_def,List.append_assoc]
lemma clauses_correct (T L : ℕ) : clauses k0 T L=(clauseOrder (K := K) T L).entries.map (clauseCode k0) := by
  simp only [clauseOrder,Ordered.map,Ordered.sum,Ordered.prod,Ordered.fin,List.map_append,List.map_map,
    List.product,List.map_flatMap,Function.comp_def,Tableau.clauseEquiv,Equiv.symm_mk,Equiv.coe_fn_mk,clauseCode]
  simp only [clauses,RoundingList.range_finRange,List.flatMap_map,List.map_map,Function.comp_def,List.append_assoc]
lemma boundaries_correct (L : ℕ) : boundaries k0 L=(boundaryOrder (K := K) L).entries.map (boundaryCode k0) := by
  have hu : (Ordered.fixed Unit).entries=[()] := by
    apply List.ext_getElem
    · rw [Ordered.length_card]; simp
    · intros; exact Subsingleton.elim _ _
  simp only [boundaryOrder,Ordered.prod,Ordered.sum,Ordered.fin,List.product,List.map_flatMap,
    List.map_append,List.map_map,Function.comp_def,boundaryCode,hu,List.map_singleton,boolOrder]
  simp only [boundaries,RoundingList.range_finRange,List.map_map,Function.comp_def]
lemma tests_correct (T L : ℕ) : tests k0 T L=(testOrder (K := K) T L).entries.map (testCode k0) := by
  rw [tests,clauses_correct,boundaries_correct]
  simp only [testOrder,Ordered.sum,List.map_append,List.map_map,Function.comp_def,testCode,Sum.elim_inl,Sum.elim_inr]
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectories

end OAI
