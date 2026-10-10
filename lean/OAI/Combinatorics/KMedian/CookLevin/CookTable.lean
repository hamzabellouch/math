import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookBoundaryProgram
import OAI.Combinatorics.KMedian.CookLevin.TableauDirectoryProgram
import OAI.Combinatorics.KMedian.CookLevin.TableauQueryProgram
import OAI.Combinatorics.KMedian.Machines.LocalCompiler
import OAI.Combinatorics.KMedian.Machines.TablePromises

namespace OAI

section Inline_PCPCookTable
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
local instance : Inhabited P.tm.K := ⟨P.tm.k₀⟩
local instance : Inhabited (Value P.tm.m) := ⟨((none,P.tm.initialState),((none,P.tm.initialState),fun _=>⟨[],Nat.zero_le _⟩),fun _=>none)⟩
local instance : Inhabited (Query P.tm.m) := ⟨q0 P.tm.m⟩
noncomputable local instance : DecidableEq (Query P.tm.m) := Classical.decEq _
noncomputable def vars (x : Word) := TableauDirectory.vars P.tm.k₀ (time P p x) (space P p x)
noncomputable def tests (x : Word) := TableauDirectory.tests P.tm.k₀ (time P p x) (space P p x)
noncomputable def query (x : Word) := rawQuery P.tm.m P.tm.k₀ (time P p x) (space P p x)
noncomputable def accept (x : Word) := rawAccept P.tm.m (boundary P p x)
noncomputable def table (x : Word) := LocalCompiler.table (vars P p) (tests P p) (query P p) (accept P p) x
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_vars : Poly (vars P p) := by
  apply poly_congr ((TableauDirectory.poly_vars P.tm.k₀).comp (Poly.pair (poly_timeUnits P p) (poly_spaceUnits P p)))
  intro x; simp only [vars,timeUnits,spaceUnits,List.length_replicate]
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_tests : Poly (tests P p) := by
  apply poly_congr ((TableauDirectory.poly_tests P.tm.k₀).comp (Poly.pair (poly_timeUnits P p) (poly_spaceUnits P p)))
  intro x; simp only [tests,timeUnits,spaceUnits,List.length_replicate]
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma poly_query : Poly (fun z : (Word×TC (K:=P.tm.K))×Query P.tm.m =>query P p z.1.1 z.1.2 z.2) := by
  exact (poly_rawQuery P.tm.m P.tm.k₀).comp
    (Poly.pair (Poly.pair (Poly.pair ((poly_time P p).comp (Poly.fst.comp Poly.fst))
      ((poly_space P p).comp (Poly.fst.comp Poly.fst))) (Poly.snd.comp Poly.fst)) Poly.snd)
lemma poly_table : Poly (table P p) := by
  have ha : Poly (fun z : Word×TC (K:=P.tm.K)=>accept P p z.1 z.2) := by
    unfold accept
    with_reducible exact poly_accept P p
  unfold table
  with_reducible
    exact LocalCompiler.poly_table (X:=Word) (VC:=VC (K:=P.tm.K)) (TC:=TC (K:=P.tm.K))
      (Q:=Query P.tm.m) (A:=Value P.tm.m) (vars P p) (tests P p) (query P p) (accept P p)
      (poly_vars P p) (poly_tests P p) (poly_query P p) ha
      (poly_code_eq (K:=P.tm.K) 3) (poly_code_eq (K:=P.tm.K) 9)
noncomputable def represents (x : Word) : (table P p x).Represents (system P p x).binary := by
  exact LocalCompiler.represents (vars P p) (tests P p) (query P p) (accept P p)
    (system P p x) (varOrder (K:=P.tm.K) (time P p x) (space P p x))
    (testOrder (K:=P.tm.K) (time P p x) (space P p x))
    (varCode P.tm.k₀) (testCode P.tm.k₀)
    (varCode_injective _ _ _) (testCode_injective _ _ _) x
    (vars_correct _ _ _) (tests_correct _ _ _)
    (rawQuery_correct _ _ _ _ _) (rawAccept_correct _ _ _ _ _)
lemma wellFormed (x : Word) : (table P p x).WellFormed := (represents P p x).wellFormed
lemma correct (x : Word) : (∃ a, ((table P p x).csp (wellFormed P p x)).Satisfies a) ↔
    ∃ w : Word, w.length≤p.eval x.length ∧ verify (x,w)=true := by
  rw [(represents P p x).satisfies,FiniteCSP.binary_iff,CookLevin.correct]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookTable

end OAI
