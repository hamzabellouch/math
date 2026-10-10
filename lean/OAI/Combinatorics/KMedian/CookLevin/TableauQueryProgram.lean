import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauDirectories
import OAI.Combinatorics.KMedian.Machines.FiniteCases

namespace OAI

section Inline_PCPTableauQueryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic Tableau Turing.TM2
open scoped Classical

variable {K : Type} {Γ : K→Type} {Λ σ : Type}
variable [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype σ] [∀k,Fintype (Γ k)]
variable (M : Λ→Stmt Γ Λ σ) (k0 : K)
noncomputable def rawQuery (T L : ℕ) (test : TC (K := K)) (q : Query M) : VC (K := K) :=
  let t := test.2.1
  let k := test.2.2.1
  let i := test.2.2.2
  if test.1=0 then (2,t,k,if q=q0 M then i else i+1)
  else if test.1=1 then (2,t,k,L)
  else if test.1=2 then
    match q with
    | .inl _ => (0,t,k0,0)
    | .inr (.inl _) => (1,t,k0,0)
    | .inr (.inr (.inl (k,j))) => (2,t,k,min j.val L)
    | _ => (0,t,k0,0)
  else if test.1=3 then if q=q0 M then (0,t+1,k0,0) else (1,t,k0,0)
  else if test.1=4 then
    match q with
    | .inl _ => (1,t,k0,0)
    | .inr (.inl _) => (2,t+1,k,i)
    | .inr (.inr (.inr h)) => (2,t,k,min (i+radius M-h.val) L)
    | _ => (1,t,k0,0)
  else if test.1=5 then (0,0,k0,0)
  else if test.1=6 then (0,T,k0,0)
  else if test.1=7 then (2,0,k,i)
  else (2,T,k,i)
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma rawQuery_clause (T L : ℕ) (c : Clause (K := K) T L) (q : Query M) :
    rawQuery M k0 T L (clauseCode k0 c) q=varCode k0 (Tableau.query M T L c q) := by
  cases c <;> rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;>
    simp [rawQuery,clauseCode,Tableau.query,varCode,q0,cell,ctrl,resp,now,later,clamp]
omit [Fintype K] [Fintype σ] [∀ k, Fintype (Γ k)] in
lemma rawQuery_boundary (T L : ℕ) (b : BoundaryClause (K := K) L) (q : Query M) :
    rawQuery M k0 T L (boundaryCode k0 b) q=varCode k0 (boundaryQuery M T L b q) := by
  rcases b with ⟨side,b⟩
  cases side <;> rcases b with b|⟨k,i⟩ <;>
    simp [rawQuery,boundaryCode,boundaryQuery,varCode,ctrl,cell,boundaryTime,time0,timeLast]
lemma rawQuery_correct (T L : ℕ) (B : Boundary (Γ := Γ) (Λ := Λ) (σ := σ))
    (c : Clause (K := K) T L ⊕ BoundaryClause (K := K) L) (q : Query M) :
    rawQuery M k0 T L (testCode k0 c) q=varCode k0 ((boundedSystem M B T L).query c q) := by
  cases c with
  | inl c => exact rawQuery_clause M k0 T L c q
  | inr b => exact rawQuery_boundary M k0 T L b q
noncomputable instance queryCoding : Coding (Query M) := finiteCoding _
noncomputable instance queryHardcoded : Hardcoded (Query M) := ⟨fun _ _ _ f => finite_function f⟩
variable [Coding K] [Hardcoded K] [Inhabited K]
omit [Fintype σ] [∀ k, Fintype (Γ k)] [Hardcoded K] in
lemma poly_rawQuery : Poly (fun p : ((ℕ×ℕ)×TC (K := K))×Query M => rawQuery M k0 p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have he (i : Fin 9) : Poly (fun t : Fin 9 => decide (t=i)) := hardcoded _
  have he' (i : Fin 9) : Poly (fun p : (ℕ×ℕ)×TC (K := K) => decide (p.2.1=i)) :=
    (he i).comp (by fun_prop)
  have hb : ∀ q : Query M, Poly (fun p : (ℕ×ℕ)×TC (K := K) => rawQuery M k0 p.1.1 p.1.2 p.2 q) := by
    intro q
    unfold rawQuery
    apply Poly.ite_prop (he' 0)
    · split_ifs <;> fun_prop
    · apply Poly.ite_prop (he' 1) (by fun_prop)
      apply Poly.ite_prop (he' 2)
      · rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;> dsimp only <;> fun_prop
      · apply Poly.ite_prop (he' 3)
        · split_ifs <;> fun_prop
        · apply Poly.ite_prop (he' 4)
          · rcases q with ⟨⟩ | ⟨⟩ | ⟨k,j⟩ | h <;> dsimp only <;> fun_prop
          · apply Poly.ite_prop (he' 5) (by fun_prop)
            apply Poly.ite_prop (he' 6) (by fun_prop)
            exact Poly.ite_prop (he' 7) (by fun_prop) (by fun_prop)
  exact (poly_finite_cases _ hb).comp (Poly.pair Poly.snd Poly.fst)
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauQueryProgram

end OAI
