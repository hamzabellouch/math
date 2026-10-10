import Mathlib
import OAI.Combinatorics.KMedian.Expanders.GraphProducts
import OAI.Combinatorics.KMedian.Machines.RawRotation

namespace OAI

section Inline_PCPRawSquare
namespace MetricKMedian.PCP.Compiler.RotationTable
open Binary Binary.Automatic

variable {D : Type} [Fintype D] [Inhabited D]
noncomputable def squareLookup (R : RotationTable D) (v : ℕ) (d : D × D) : ℕ × (D × D) :=
  let q := lookup R v d.1
  let r := lookup R q.1 d.2
  (r.1,(r.2,q.2))
noncomputable def fourthLookup (R : RotationTable D) (v : ℕ) (d : (D × D) × (D × D)) : ℕ × ((D × D) × (D × D)) :=
  let q := squareLookup R v d.1
  let r := squareLookup R q.1 d.2
  (r.1,(r.2,q.2))
variable [Coding D] [Hardcoded D]
@[fun_prop] lemma poly_squareLookup : Poly (fun p : (RotationTable D × ℕ) × (D × D) => squareLookup p.1.1 p.1.2 p.2) := by
  unfold squareLookup
  have hl := poly_lookup (D := D)
  fun_prop
@[fun_prop] lemma poly_fourthLookup : Poly (fun p : (RotationTable D × ℕ) × ((D × D) × (D × D)) => fourthLookup p.1.1 p.1.2 p.2) := by
  unfold fourthLookup squareLookup
  have hl := poly_lookup (D := D)
  fun_prop
lemma poly_fourthLookup_comp {X : Type} [Coding X] (R : X → RotationTable D) (v : X → ℕ)
    (d : X → ((D × D) × (D × D))) (hR : Poly R) (hv : Poly v) (hd : Poly d) :
    Poly (fun x => fourthLookup (R x) (v x) (d x)) :=
  poly_fourthLookup.comp (Poly.pair (Poly.pair hR hv) hd)
omit [Coding D] [Hardcoded D]
lemma squareLookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : D × D) :
    squareLookup (table G e) (e v).val d=((e (G.square.step v d)).val,G.square.back v d) := by
  simp only [squareLookup,lookup_table]
  rfl
lemma fourthLookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : (D × D) × (D × D)) :
    fourthLookup (table G e) (e v).val d=((e (G.square.square.step v d)).val,G.square.square.back v d) := by
  simp only [fourthLookup,squareLookup_table]
  rfl
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRawSquare

end OAI
