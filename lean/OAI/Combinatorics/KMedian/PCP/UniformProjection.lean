import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookAmplify
import OAI.Combinatorics.KMedian.CookLevin.SeedInput
import OAI.Combinatorics.KMedian.CookLevin.SemanticProjection
import OAI.Combinatorics.KMedian.Hardness.ProjectionReduction

namespace OAI

section Inline_PCPUniformProjection
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
local instance (x : Word) : Nonempty (Fin (amplified P p x).2.length) :=
  Fin.pos_iff_nonempty.mp (amplified_valid P p x).1
noncomputable def projection (n : ℕ) (x : Word) :
    Coverage.ProjectionInput (SeedProgram.Width n) (SeedProgram.LeftSize n) (SeedProgram.RightSize n) :=
  SeedProgram.output (amplified P p x) (amplified_valid P p x) n
noncomputable def projectionProgram (n : ℕ) :
    PolyProgram id Coverage.ProjectionInput.encode (projection P p n) :=
  (BooleanLists.packProgram.comp ((SeedProgram.poly_output_raw n).comp (poly_amplified P p)).program).recode
    id (fun _=>rfl) (fun x=>by
      change enc (ProjectionTable.raw (SeedProgram.leftOrder.nested n) (SeedProgram.rightOrder.nested n)
        (ProjectionTable.power (SeedProgram.seedTable (amplified P p x)) n))=enc (projection P p n x).raw
      rw [projection,SeedProgram.output_raw])
lemma projection_poly (n : ℕ) : FinitePolyTime id Coverage.ProjectionInput.encode (projection P p n) :=
  ⟨(projectionProgram P p n).stock,(projectionProgram P p n).finite_work⟩
lemma projection_complete (n : ℕ) (x : Word)
    (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) : (projection P p n x).Perfect :=
  SeedProgram.output_perfect _ _ n (amplified_complete P p x hx)
lemma projection_sound (n : ℕ) (x : Word)
    (hx : ¬∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true)
    (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (projection P p n x).Sound ε :=
  SeedProgram.output_sound _ _ n (amplified_sound P p x hx) ε hε hn
end MetricKMedian.PCP.Compiler.CookProgram
namespace MetricKMedian.Coverage
open Complexity PCP PCP.Compiler
open scoped Classical

theorem projection_gap_np_reductions : ProjectionGapNPReductions := by
  intro ε hε L hL
  obtain ⟨verify,p,⟨P,hfinite⟩,hverify⟩ := hL
  let (k : P.tm.K) : Finite (P.tm.Γ k) := hfinite k
  let (k : P.tm.K) : Fintype (P.tm.Γ k) := Fintype.ofFinite _
  have he : (0:ℝ)<(ε:ℝ) := Rat.cast_pos.mpr hε
  obtain ⟨n,hn⟩ := ProjectionSeed.repetition_exists (ε:ℝ) he
  refine ⟨SeedProgram.Width n,SeedProgram.LeftSize n,SeedProgram.RightSize n,
    CookProgram.projection P p n,CookProgram.projection_poly P p n,?_,?_⟩
  · intro x hx
    exact CookProgram.projection_complete P p n x ((hverify x).mp hx)
  · intro x hx
    apply CookProgram.projection_sound P p n x _ (ε:ℝ) he.le hn
    intro hc
    exact hx ((hverify x).mpr hc)
end MetricKMedian.Coverage

end Inline_PCPUniformProjection

end OAI
