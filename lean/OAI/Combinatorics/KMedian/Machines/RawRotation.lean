import Mathlib
import OAI.Combinatorics.KMedian.Expanders.PortWalk
import OAI.Combinatorics.KMedian.Machines.Hardcoded

namespace OAI

section Inline_PCPRawRotation

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

abbrev RotationTable (D : Type) := List (List (ℕ × D))
namespace RotationTable
variable {D : Type} [Fintype D] [Inhabited D]
noncomputable def ports : List D := List.ofFn (Fintype.equivFin D).symm
omit [Inhabited D] in
@[simp] lemma ports_length : (ports (D := D)).length=Fintype.card D := List.length_ofFn
noncomputable def lookup (R : RotationTable D) (v : ℕ) (d : D) : ℕ × D :=
  (R[v]?.getD [])[((Fintype.equivFin D) d).val]?.getD (0,default)
noncomputable def table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) : RotationTable D :=
  List.ofFn (fun i : Fin N => ports.map (fun d => ((e (G.step (e.symm i) d)).val,G.back (e.symm i) d)))
omit [Inhabited D] in
@[simp] lemma table_length {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) :
    (table G e).length=N := List.length_ofFn
lemma lookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : D) :
    lookup (table G e) (e v).val d=((e (G.step v d)).val,G.back v d) := by
  simp only [lookup,table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,
    Fin.eta,Equiv.symm_apply_apply,ports,List.map_ofFn]
  simp only [Function.comp_def,Equiv.symm_apply_apply]
variable [Coding D] [Hardcoded D]
lemma poly_lookup : Poly (fun s : RotationTable D × (ℕ × D) => lookup s.1 s.2.1 s.2.2) := by
  unfold lookup
  apply Poly.list_getD_comp
  · exact Poly.list_getD_comp [] Poly.fst (Poly.fst.comp Poly.snd)
  · exact (hardcoded (fun d : D => (Fintype.equivFin D d).val)).comp (Poly.snd.comp Poly.snd)
lemma poly_lookup_comp {A : Type} [Coding A] {R : A → RotationTable D} {v : A → ℕ} {d : A → D}
    (hR : Poly R) (hv : Poly v) (hd : Poly d) : Poly (fun a => lookup (R a) (v a) (d a)) :=
  poly_lookup.comp (Poly.pair hR (Poly.pair hv hd))
end RotationTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawRotation

end OAI
