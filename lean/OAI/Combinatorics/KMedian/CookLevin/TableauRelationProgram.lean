import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauDirectories
import OAI.Combinatorics.KMedian.Machines.LocalCompiler

namespace OAI

section Inline_PCPTableauRelationProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
abbrev RelationSet := Finset (Query M→Value M)
noncomputable def firstControlSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).1=B.firstControl)
noncomputable def lastControlSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).1=(B.last.l,B.last.var))
noncomputable def firstCellSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (k : K) (i : ℕ) : RelationSet M :=
  Finset.univ.filter (fun z => prefixCell (B.firstPrefix k) (B.certificateBound k) i ((z (q0 M)).2.2 k))
noncomputable def lastCellSet (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (k : K) (i : ℕ) : RelationSet M :=
  Finset.univ.filter (fun z => (z (q0 M)).2.2 k=(B.last.stk k)[i]?)
noncomputable def rawAccept (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (test : TC (K := K)) : RelationSet M :=
  let k := test.2.2.1
  let i := test.2.2.2
  if test.1=0 then Finset.univ.filter (fun z => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none)
  else if test.1=1 then Finset.univ.filter (fun z => (z (q0 M)).2.2 k=none)
  else if test.1=2 then Finset.univ.filter (fun z => PrefixRelation M (z (q0 M)).1 (fun k i => (z (qtop M k i)).2.2 k) (z (q1 M)).2.1)
  else if test.1=3 then Finset.univ.filter (fun z => (z (q0 M)).1=(z (q1 M)).2.1.1)
  else if test.1=4 then Finset.univ.filter (fun z => (z (q1 M)).2.2 k=cellTable M k (category M i) ((z (q0 M)).2.1.2 k) (fun h => (z (qwin M h)).2.2 k))
  else if test.1=5 then firstControlSet M B
  else if test.1=6 then lastControlSet M B
  else if test.1=7 then firstCellSet M B k i
  else lastCellSet M B k i
lemma rawAccept_clause (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (c : Clause (K := K) T L) :
    rawAccept M B (clauseCode k0 c)=(Tableau.system M T L).accept c := by
  cases c <;> ext z <;> simp +instances [rawAccept,clauseCode,Tableau.system,relation]
  all_goals exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
lemma rawAccept_boundary (L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ)) (b : BoundaryClause (K := K) L) :
    rawAccept M B (boundaryCode k0 b)=Finset.univ.filter (boundaryRelation M B L b) := by
  rcases b with ⟨side,b⟩
  cases side <;> rcases b with b|⟨k,i⟩ <;> ext z
  all_goals simp [rawAccept,boundaryCode,boundaryRelation,firstControlSet,lastControlSet,firstCellSet,lastCellSet]
  all_goals rfl
lemma rawAccept_correct (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (c : Clause (K := K) T L ⊕ BoundaryClause (K := K) L) :
    rawAccept M B (testCode k0 c)=(boundedSystem M B T L).accept c := by
  cases c with
  | inl c => exact rawAccept_clause M k0 T L B c
  | inr b => exact rawAccept_boundary M k0 L B b
omit [Fintype K] [DecidableEq K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma poly_category : Poly (category M) := by
  have hi : Poly (fun i : ℕ => min i (2*radius M)) := by fun_prop
  have hh := Poly.list_getD_comp (⟨0,by omega⟩ : Fin (2*radius M+1))
    (Automatic.Poly.const (List.finRange (2*radius M+1))) hi
  apply poly_congr hh
  intro i
  rw [List.getElem?_eq_getElem (by simp only [List.length_finRange]; omega)]
  simp only [Option.getD_some,List.getElem_finRange,category,Fin.ext_iff,Fin.val_cast]
variable {X : Type} [Coding X] [Coding K] [Hardcoded K]
lemma poly_rawAccept (B : X→Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (hf : Poly (fun x => firstControlSet M (B x)))
    (hl : Poly (fun x => lastControlSet M (B x)))
    (hfc : Poly (fun p : (X×K)×ℕ => firstCellSet M (B p.1.1) p.1.2 p.2))
    (hlc : Poly (fun p : (X×K)×ℕ => lastCellSet M (B p.1.1) p.1.2 p.2)) :
    Poly (fun p : X×TC (K := K) => rawAccept M (B p.1) p.2) := by
  have he (i : Fin 9) : Poly (fun t : Fin 9 => decide (t=i)) := hardcoded _
  have hs : Poly (fun k : K => Finset.univ.filter (fun z : Query M→Value M => (z (q0 M)).2.2 k=none → (z (q1 M)).2.2 k=none)) := hardcoded _
  have hn : Poly (fun k : K => Finset.univ.filter (fun z : Query M→Value M => (z (q0 M)).2.2 k=none)) := hardcoded _
  have hu : Poly (fun p : K×Fin (2*radius M+1) => Finset.univ.filter (fun z : Query M→Value M =>
    (z (q1 M)).2.2 p.1=cellTable M p.1 p.2 ((z (q0 M)).2.1.2 p.1) (fun h => (z (qwin M h)).2.2 p.1))) := hardcoded _
  have hc := poly_category M
  have he' (i : Fin 9) : Poly (fun p : X×TC (K := K) => decide (p.2.1=i)) :=
    (he i).comp (by fun_prop)
  unfold rawAccept
  apply Poly.ite_prop (he' 0)
  · exact hs.comp (by fun_prop)
  apply Poly.ite_prop (he' 1)
  · exact hn.comp (by fun_prop)
  apply Poly.ite_prop (he' 2) (Automatic.Poly.const _)
  apply Poly.ite_prop (he' 3) (Automatic.Poly.const _)
  apply Poly.ite_prop (he' 4)
  · exact hu.comp (Poly.pair (by fun_prop) (hc.comp (by fun_prop)))
  apply Poly.ite_prop (he' 5) (hf.comp Poly.fst)
  apply Poly.ite_prop (he' 6) (hl.comp Poly.fst)
  exact Poly.ite_prop (he' 7) (hfc.comp (show Poly (fun p : X×TC (K := K) => ((p.1,p.2.2.2.1),p.2.2.2.2)) by fun_prop))
    (hlc.comp (show Poly (fun p : X×TC (K := K) => ((p.1,p.2.2.2.1),p.2.2.2.2)) by fun_prop))
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauRelationProgram

end OAI
