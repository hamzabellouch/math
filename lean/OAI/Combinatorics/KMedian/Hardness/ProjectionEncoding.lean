import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists
import OAI.Combinatorics.KMedian.Hardness.Encoding
import OAI.Combinatorics.KMedian.Hardness.ProjectionInput
import OAI.Combinatorics.KMedian.Process.RoundingListOperations

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

abbrev ProjectionRaw := List Bool × List (List (ℕ × List ℕ))
abbrev BlockCode := List ℕ × List ℕ

namespace ProjectionRaw

def lefts (R : ProjectionRaw) : List ℕ := List.range R.1.length
def rights (R : ProjectionRaw) : List ℕ := List.range R.2.length

def edge (R : ProjectionRaw) (v i : ℕ) : ℕ × List ℕ :=
  (((R.2[v]?).getD [])[i]?).getD (0,[])

def test (R : ProjectionRaw) (v : ℕ) (sw : BlockCode) (u a j : ℕ) : Bool :=
  let e := R.edge v ((sw.1[j]?).getD 0)
  decide (e.1 = u) && decide ((sw.2[(e.2[a]?).getD 0]?).getD 0 = j)

def incident (D : ℕ) (R : ProjectionRaw) (v : ℕ) (sw : BlockCode) (u a : ℕ) : Bool :=
  !((List.range D).filter (fun j => R.test v sw u a j)).isEmpty

@[fun_prop] theorem lefts_poly : Poly lefts := by
  unfold lefts; apply Poly.comp Poly.list_indices; fun_prop
@[fun_prop] theorem rights_poly : Poly rights := by
  unfold rights; apply Poly.comp Poly.list_indices; fun_prop
@[fun_prop] theorem edge_poly : Poly (fun x : ProjectionRaw × ℕ × ℕ => x.1.edge x.2.1 x.2.2) := by
  unfold edge; fun_prop
@[fun_prop] theorem test_poly : Poly (fun x : ProjectionRaw × ℕ × BlockCode × ℕ × ℕ × ℕ =>
    x.1.test x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  unfold test; fun_prop
@[fun_prop] theorem incident_poly (D : ℕ) : Poly (fun x : ProjectionRaw × ℕ × BlockCode × ℕ × ℕ =>
    incident D x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold incident
  have ht : Poly (fun x : (ProjectionRaw × ℕ × BlockCode × ℕ × ℕ) × ℕ =>
      x.1.1.test x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 x.2) :=
    Poly.comp (g := fun x : (ProjectionRaw × ℕ × BlockCode × ℕ × ℕ) × ℕ =>
      (x.1.1,x.1.2.1,x.1.2.2.1,x.1.2.2.2.1,x.1.2.2.2.2,x.2)) test_poly (by fun_prop)
  fun_prop

noncomputable def blocks (r b D : ℕ) : List BlockCode :=
  List.ofFn (fun x : Fin (ProjectionInput.width r b D) =>
    let sw := (ProjectionInput.blockEquiv r b D).symm x
    (List.ofFn (fun j => (sw.1 j).val),List.ofFn (fun c => (sw.2 c).val)))

def table (a D : ℕ) (cs : List BlockCode) (R : ProjectionRaw) : List Bool :=
  R.rights.flatMap (fun v => cs.flatMap (fun sw =>
    R.lefts.flatMap (fun u => (List.range a).map (fun c => incident D R v sw u c))))

@[fun_prop] theorem table_poly (a D : ℕ) (cs : List BlockCode) : Poly (table a D cs) := by
  have hentry : Poly (fun x : ((ProjectionRaw × ℕ × BlockCode) × ℕ) × ℕ =>
      incident D x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.1.2 x.2) :=
    Poly.comp (g := fun x : ((ProjectionRaw × ℕ × BlockCode) × ℕ) × ℕ =>
      (x.1.1.1,x.1.1.2.1,x.1.1.2.2,x.1.2,x.2)) (incident_poly D) (by fun_prop)
  have hlabel : Poly (fun x : (ProjectionRaw × ℕ × BlockCode) × ℕ =>
      (List.range a).map (fun c => incident D x.1.1 x.1.2.1 x.1.2.2 x.2 c)) :=
    Poly.list_map hentry (by fun_prop)
  have hu : Poly (fun x : ProjectionRaw × ℕ × BlockCode =>
      x.1.lefts.flatMap (fun u => (List.range a).map (fun c => incident D x.1 x.2.1 x.2.2 u c))) :=
    Poly.list_flatMap hlabel (Poly.comp lefts_poly Poly.fst)
  have hsw : Poly (fun x : (ProjectionRaw × ℕ) × BlockCode =>
      x.1.1.lefts.flatMap (fun u => (List.range a).map (fun c =>
        incident D x.1.1 x.1.2 x.2 u c))) :=
    Poly.comp (g := fun x : (ProjectionRaw × ℕ) × BlockCode =>
      (x.1.1,x.1.2,x.2)) hu (by fun_prop)
  have hv : Poly (fun x : ProjectionRaw × ℕ => cs.flatMap (fun sw =>
      x.1.lefts.flatMap (fun u => (List.range a).map (fun c => incident D x.1 x.2 sw u c)))) :=
    Poly.list_flatMap hsw (by fun_prop)
  exact Poly.list_flatMap hv rights_poly

noncomputable def bytes (r a b D : ℕ) (R : ProjectionRaw) : List Bool :=
  encodeNat (R.2.length * ProjectionInput.width r b D) ++
  encodeNat (R.1.length * a) ++ encodeNat R.1.length ++
  table a D (blocks r b D) R

@[fun_prop] theorem bytes_poly (r a b D : ℕ) : Poly (bytes r a b D) := by
  have ht : Poly (table a D (blocks r b D)) := table_poly a D _
  unfold bytes
  fun_prop

noncomputable def program (r a b D : ℕ) :
    PolyProgram enc id (bytes r a b D) :=
  PolyProgram.comp (f := bytes r a b D) (g := id)
    (bytes_poly r a b D).program BooleanLists.unpackProgram

end ProjectionRaw

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

def raw : ProjectionRaw :=
  (List.replicate G.u false,
    List.ofFn (fun v => List.ofFn (fun i =>
      ((G.system.neighbor v i).val,List.ofFn (fun c => (G.system.project v i c).val)))))

def encode : List Bool := enc G.raw

@[simp] theorem raw_lefts : G.raw.lefts = List.range G.u := by
  simp [raw,ProjectionRaw.lefts]
@[simp] theorem raw_rights : G.raw.rights = List.range G.v := by
  simp [raw,ProjectionRaw.rights]

@[simp] theorem raw_edge (v : Fin G.v) (i : Fin r) :
    G.raw.edge v.val i.val =
      ((G.system.neighbor v i).val,List.ofFn (fun c => (G.system.project v i c).val)) := by
  simp only [raw,ProjectionRaw.edge,List.getElem?_ofFn,dite_eq_left v.isLt,
    dite_eq_left i.isLt,Option.getD_some]

theorem raw_test (D : ℕ) (v : Fin G.v)
    (s : Fin D → Fin r) (w : Fin b → Fin D) (u : Fin G.u) (c : Fin a) (j : Fin D) :
    G.raw.test v.val (List.ofFn (fun i => (s i).val),List.ofFn (fun e => (w e).val))
      u.val c.val j.val =
      decide (G.system.neighbor v (s j) = u ∧ w (G.system.project v (s j) c) = j) := by
  simp only [ProjectionRaw.test,List.getElem?_ofFn,dite_eq_left j.isLt,Option.getD_some,
    G.raw_edge,dite_eq_left c.isLt,dite_eq_left (G.system.project v (s j) c).isLt,
    Fin.val_inj]
  exact (Bool.decide_and _ _).symm

theorem raw_incident (D : ℕ) (hD : 0 < D) (v : Fin G.v)
    (s : Fin D → Fin r) (w : Fin b → Fin D) (u : Fin G.u) (c : Fin a) :
    ProjectionRaw.incident D G.raw v.val
      (List.ofFn (fun i => (s i).val),List.ofFn (fun e => (w e).val)) u.val c.val =
      (G.toCoverage D hD).incident (G.clientEquiv D ((v,s),w)) (G.facilityEquiv (u,c)) := by
  apply Bool.eq_iff_iff.mpr
  rw [G.incident_equiv]
  simp only [ProjectionRaw.incident,Bool.not_eq_true',List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter,List.mem_range]
  constructor
  · rintro ⟨j,hj,ht⟩
    have hh := G.raw_test D v s w u c ⟨j,hj⟩
    rw [hh,decide_eq_true_eq] at ht
    exact ⟨⟨j,hj⟩,ht⟩
  · rintro ⟨j,hj⟩
    refine ⟨j.val,j.isLt,?_⟩
    rw [G.raw_test,decide_eq_true_eq]
    exact hj

theorem ofFn_product {α : Type} {m n : ℕ} (f : Fin (m*n) → α) :
    List.ofFn f = (List.finRange m).flatMap (fun i => (List.finRange n).map
      (fun j => f (finProdFinEquiv (i,j)))) := by
  rw [List.ofFn_mul,List.flatMap_def,← List.ofFn_eq_map]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  change i.val*n+j.val = j.val+n*i.val
  ring

@[simp] theorem client_block (D : ℕ) (v : Fin G.v) (x : Fin (width r b D)) :
    G.clientEquiv D ((v,((blockEquiv r b D).symm x).1),
      ((blockEquiv r b D).symm x).2) = finProdFinEquiv (v,x) := by
  simp [clientEquiv]

theorem table_correct (D : ℕ) (hD : 0 < D) :
    ProjectionRaw.table a D (ProjectionRaw.blocks r b D) G.raw =
      (List.ofFn (fun x => List.ofFn ((G.toCoverage D hD).incident x))).flatten := by
  have hp (x : Fin (G.v * width r b D)) :
      List.ofFn ((G.toCoverage D hD).incident x) =
      (List.finRange G.u).flatMap (fun u => (List.finRange a).map
        (fun c => (G.toCoverage D hD).incident x (G.facilityEquiv (u,c)))) :=
    ofFn_product _
  rw [ofFn_product]
  simp only [hp,List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_map,Function.id_def]
  unfold ProjectionRaw.table ProjectionRaw.blocks
  rw [G.raw_lefts,G.raw_rights]
  simp only [RoundingList.range_finRange,List.ofFn_eq_map,List.flatMap_map,List.map_map,
    Function.comp_def]
  congr 1
  funext v
  congr 1
  funext x
  congr 1
  funext u
  congr 1
  funext c
  simpa only [G.client_block,List.ofFn_eq_map] using G.raw_incident D hD v
    ((blockEquiv r b D).symm x).1 ((blockEquiv r b D).symm x).2 u c

theorem bytes_correct (D : ℕ) (hD : 0 < D) :
    ProjectionRaw.bytes r a b D G.raw = (G.toCoverage D hD).encode := by
  unfold ProjectionRaw.bytes
  rw [G.table_correct D hD]
  simp only [raw,List.length_replicate,List.length_ofFn,Input.encode]

noncomputable def coverageProgram (D : ℕ) (hD : 0 < D) :
    PolyProgram (encode (r:=r) (a:=a) (b:=b)) Input.encode (fun G => G.toCoverage D hD) :=
  (ProjectionRaw.program r a b D).recode raw (fun _ => rfl)
    (fun G => by exact G.bytes_correct D hD)

theorem coverage_finite_poly (D : ℕ) (hD : 0 < D) :
    Complexity.FinitePolyTime (encode (r:=r) (a:=a) (b:=b)) Input.encode
      (fun G => G.toCoverage D hD) :=
  ⟨coverageProgram D hD |>.stock,coverageProgram D hD |>.finite_work⟩

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
