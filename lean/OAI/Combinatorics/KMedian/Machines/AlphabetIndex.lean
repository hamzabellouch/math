import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PaddedAlphabet
import OAI.Combinatorics.KMedian.Machines.RawCSP

namespace OAI

section Inline_PCPAlphabetIndex
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable instance sampleCoding : Coding (EdgeSample K) := finiteCoding _
noncomputable instance sampleHardcoded : Hardcoded (EdgeSample K) := ⟨fun _ _ _ f => finite_function f⟩
noncomputable instance sampleInhabited : Inhabited (EdgeSample K) := Classical.inhabited_of_nonempty inferInstance
abbrev Tag := EdgeSample K × Fin 4
noncomputable def B : ℕ := Fintype.card (BitVector K)
noncomputable def I : ℕ := Fintype.card (UniversalInterior K)
noncomputable def S : ℕ := Fintype.card (EdgeSample K)
noncomputable def bitIndex (b : BitVector K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def intIndex (b : UniversalInterior K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def sampleIndex (b : EdgeSample K) : ℕ := (Fintype.equivFin _ b).val
noncomputable def nodeEquiv (nv ne : ℕ) : PaddedNode (Fin nv) (Fin ne) K ≃
    Fin ((nv*B K+ne*I K)+ne*S K) :=
  (Equiv.sumCongr
    ((Equiv.sumCongr
      ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)
      ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)).trans finSumFinEquiv)
    ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin _)).trans finProdFinEquiv)).trans finSumFinEquiv
lemma nodeEquiv_vertex (nv ne : ℕ) (v : Fin nv) (b : BitVector K) :
    (nodeEquiv K nv ne (.inl (.inl (v,b)))).val=bitIndex K b+B K*v.val := rfl
lemma nodeEquiv_interior (nv ne : ℕ) (e : Fin ne) (b : UniversalInterior K) :
    (nodeEquiv K nv ne (.inl (.inr (e,b)))).val=nv*B K+(intIndex K b+I K*e.val) := rfl
lemma nodeEquiv_test (nv ne : ℕ) (e : Fin ne) (b : EdgeSample K) :
    (nodeEquiv K nv ne (.inr (e,b))).val=nv*B K+ne*I K+(sampleIndex K b+S K*e.val) := rfl
abbrev Label := IncidenceReduction.Label
noncomputable def positionInfo (R : Relations K) : LocalRelation.LocalPosition (R : LocalRelation.Relation K) → Fin 3 × ℕ
  | .inl x => (2,intIndex K ⟨R,.inl x⟩)
  | .inr (.inl x) => (2,intIndex K ⟨R,.inr x⟩)
  | .inr (.inr (b,x)) => (if b=0 then 0 else 1,bitIndex K x)
noncomputable def info (R : Relations K) (z : Tag K) : Fin 3 × ℕ :=
  positionInfo K R ((LocalRelation.query (R : LocalRelation.Relation K) z.1.1 (z.1.2 R z.1.1)).address z.2)
noncomputable def allowed (R : Relations K) (z : Tag K) : Finset (Label × Label) :=
  Finset.univ.filter (fun p => (LocalRelation.query (R : LocalRelation.Relation K) z.1.1
    (z.1.2 R z.1.1)).accept p.1=true ∧ p.1 z.2=p.2 0)
@[fun_prop] lemma poly_info : Poly (fun p : Relations K × Tag K => info K p.1 p.2) := hardcoded _
@[fun_prop] lemma poly_allowed : Poly (fun p : Relations K × Tag K => allowed K p.1 p.2) := hardcoded _
@[fun_prop] lemma poly_sampleIndex : Poly (sampleIndex K) := hardcoded _
noncomputable def endpoint (nv : ℕ) (e : ℕ) (r : CSPRow (BitVector K)) (q : Fin 3 × ℕ) : ℕ :=
  if q.1=0 then q.2+B K*r.1 else if q.1=1 then q.2+B K*r.2.1 else nv*B K+(q.2+I K*e)
noncomputable def row (s : CSPTable (BitVector K)) (e : ℕ) (z : Tag K) : CSPRow Label :=
  (s.1.length*B K+s.2.length*I K+(sampleIndex K z.1+S K*e),
    endpoint K s.1.length e (CSPTable.row s e) (info K (CSPTable.row s e).2.2 z),
    allowed K (CSPTable.row s e).2.2 z)
@[fun_prop] lemma poly_endpoint : Poly (fun p : ((ℕ × ℕ) × CSPRow (BitVector K)) × (Fin 3 × ℕ) =>
    endpoint K p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold endpoint
  have h0 : Poly (fun i : Fin 3 => decide (i=0)) := hardcoded _
  have h1 : Poly (fun i : Fin 3 => decide (i=1)) := hardcoded _
  apply Poly.ite_prop (h0.comp (Poly.fst.comp Poly.snd))
  · fun_prop
  · apply Poly.ite_prop (h1.comp (Poly.fst.comp Poly.snd)) <;> fun_prop
@[fun_prop] lemma poly_row : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => row K p.1.1 p.1.2 p.2) := by
  unfold row
  have hg : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => CSPTable.row p.1.1 p.1.2) :=
    (CSPTable.poly_row (A := BitVector K)).comp Poly.fst
  have hR := Poly.snd.comp (Poly.snd.comp hg)
  have hq := (poly_info K).comp (Poly.pair hR Poly.snd)
  have ha := (poly_allowed K).comp (Poly.pair hR Poly.snd)
  have he := (poly_endpoint K).comp (Poly.pair (Poly.pair
    (Poly.pair (Poly.list_length.comp (Poly.fst.comp (Poly.fst.comp Poly.fst)))
      (Poly.snd.comp Poly.fst)) hg) hq)
  apply Poly.pair _ (Poly.pair he ha)
  have hsample : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => sampleIndex K p.2.1) :=
    (poly_sampleIndex K).comp (Poly.fst.comp Poly.snd)
  fun_prop
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetIndex

end OAI
