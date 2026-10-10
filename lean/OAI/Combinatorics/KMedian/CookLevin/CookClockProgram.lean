import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookLevin
import OAI.Combinatorics.KMedian.Machines.UnaryPolynomial

namespace OAI

section Inline_PCPCookClockProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau
open scoped Classical

lemma poly_encodeNat : Poly (MetricKMedian.encodeNat) := by
  have hb : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
  have ht : Poly (fun n : ℕ => n.bits.map (fun _=>true)) := Poly.list_map (Automatic.Poly.const _) hb
  apply poly_congr (Poly.list_append.comp (Poly.pair
    (Poly.list_append.comp (Poly.pair ht (Automatic.Poly.const [false]))) hb))
  intro n
  simp only [MetricKMedian.encodeNat,List.map_const',List.append_assoc]
lemma poly_firstWord : Poly CookLevin.firstWord := by
  exact Poly.list_append.comp (Poly.pair (poly_encodeNat.comp Poly.list_length) Poly.identity)
variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
noncomputable def inputUnits (x : Word) : List Unit := List.replicate (inputSize p x) ()
noncomputable def timeUnits (x : Word) : List Unit := List.replicate (time P p x) ()
noncomputable def spaceUnits (x : Word) : List Unit := List.replicate (space P p x) ()
lemma poly_wordUnits : Poly (fun x : Word => x.map (fun _=>())) := Poly.list_map (Automatic.Poly.const _) Poly.identity
lemma poly_inputUnits : Poly (inputUnits p) := by
  have h1 := poly_wordUnits.comp poly_firstWord
  have h2 := (poly_unaryPolynomial p).comp poly_wordUnits
  apply poly_congr (Poly.list_append.comp (Poly.pair h1 h2))
  intro x
  apply unitList_eq_length
  simp only [List.length_append,List.length_map,List.length_replicate,inputUnits,inputSize]
lemma poly_timeUnits : Poly (timeUnits P p) := by
  apply poly_congr ((poly_unaryPolynomial P.time).comp (poly_inputUnits p))
  intro x
  simp only [inputUnits,List.length_replicate,timeUnits,time]
lemma poly_spaceUnits : Poly (spaceUnits P p) := by
  have hr : Poly (fun x : Word => (timeUnits P p x).flatMap (fun _=>List.replicate (radius P.tm.m) ())) :=
    Poly.list_flatMap (Automatic.Poly.const _) (poly_timeUnits P p)
  apply poly_congr (Poly.list_append.comp (Poly.pair
    (Poly.list_append.comp (Poly.pair (poly_inputUnits p) hr)) (Automatic.Poly.const [()])))
  intro x
  apply unitList_eq_length
  simp only [List.length_append,List.length_singleton,spaceUnits,List.length_replicate,inputUnits]
  rw [length_flatMap_uniform _ _ (radius P.tm.m) (by intros; simp)]
  simp only [timeUnits,List.length_replicate,space,Nat.mul_comm]
lemma poly_time : Poly (time P p) := by
  apply poly_congr (Poly.list_length.comp (poly_timeUnits P p))
  intro x; simp only [timeUnits,List.length_replicate]
lemma poly_space : Poly (space P p) := by
  apply poly_congr (Poly.list_length.comp (poly_spaceUnits P p))
  intro x; simp only [spaceUnits,List.length_replicate]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookClockProgram

end OAI
