import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookLevin
import OAI.Combinatorics.KMedian.CookLevin.InitialAlphabet

namespace OAI

section Inline_PCPCookBox

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
noncomputable instance valueInhabited : Inhabited (Value P.tm.m) :=
  ⟨((none,P.tm.initialState),((none,P.tm.initialState),fun _ => ⟨[],by simp⟩),fun _ => none)⟩
abbrev Variable (x : Word) := Var (K := P.tm.K) (time P p x) (space P p x)
abbrev Test (x : Word) := Clause (K := P.tm.K) (time P p x) (space P p x) ⊕ BoundaryClause (K := P.tm.K) (space P p x)
abbrev Alphabet := FiniteCSP.Label (Q := Query P.tm.m) (A := Value P.tm.m)
noncomputable instance testNonempty (x : Word) : Nonempty (Test P p x) :=
  ⟨Sum.inr (false,Sum.inl ())⟩
noncomputable def box (x : Word) : Amplifier.Box :=
  InitialAlphabet.box (Alphabet P) (system P p x).binary
lemma box_correct (x : Word) : (box P p x).Perfect ↔
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true :=
  ((InitialAlphabet.box_iff (Alphabet P) (system P p x).binary).trans
    (system P p x).binary_iff).trans (correct P p x)
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookBox

end OAI
