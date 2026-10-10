import Mathlib
import OAI.Combinatorics.KMedian.Amplification.AmplifierCompiler
import OAI.Combinatorics.KMedian.CookLevin.CookTable
import OAI.Combinatorics.KMedian.CookLevin.InitialTable

namespace OAI

section Inline_PCPCookAmplify
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance : DecidableEq (Query P.tm.m) := Classical.decEq _
noncomputable def initial (x : Word) : CSPTable Label := InitialProgram.table (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m)) (table P p x)
lemma poly_initial : Poly (initial P p) :=
  (InitialProgram.poly_table (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m))).comp (poly_table P p)
lemma initial_valid (x : Word) : (initial P p x).WellFormed :=
  InitialProgram.valid (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m)) (table P p x) (wellFormed P p x)
lemma initial_correct (x : Word) : (∃ a, ((initial P p x).csp (initial_valid P p x)).Satisfies a) ↔
    ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true := by
  exact (InitialProgram.correct (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m))
    (table P p x) (wellFormed P p x)).trans (correct P p x)
noncomputable def amplified (x : Word) : CSPTable Label := AmplifierProgram.generate (initial P p x)
lemma poly_amplified : Poly (amplified P p) := AmplifierProgram.poly_generate.comp (poly_initial P p)
lemma amplified_valid (x : Word) : (amplified P p x).WellFormed := AmplifierProgram.generate_valid _
lemma amplified_complete (x : Word) (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) :
    ∃ a, ((amplified P p x).csp (amplified_valid P p x)).Satisfies a :=
  AmplifierProgram.generate_complete (initial_valid P p x) ((initial_correct P p x).mpr hx)
lemma amplified_sound (x : Word) (hx : ¬∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) :
    ∀ a, 1/(capLoss:ℝ)≤((amplified P p x).csp (amplified_valid P p x)).rejection a :=
  AmplifierProgram.generate_sound (initial_valid P p x) (mt (initial_correct P p x).mp hx)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
