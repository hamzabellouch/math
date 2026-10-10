import Mathlib
import OAI.Computability.VertexCover.Machines.NatDiv
import OAI.Computability.VertexCover.Machines.TableBase

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                 
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

namespace ExpandMachine

abbrev Input (q : ℕ) := Σ v, ExpanderTables.Table v q
abbrev Data := ℕ × List ℕ
def dataCode : Data → List Bool := prodBits natBits (listBits natBits)
def erase {q : ℕ} (T : Input q) : Data := (T.1,T.2.rows.toList.map Fin.val)
def code {q : ℕ} (T : Input q) : List Bool := dataCode (erase T)

def lookup (q : ℕ) (p : List ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  let r := p.1.getD (p.2.2+q*p.2.1) 0
  (r/q,r%q)

noncomputable def lookupPoly (q : ℕ) :
    Poly (prodBits (listBits natBits) (prodBits natBits natBits)) (prodBits natBits natBits) (lookup q) := by
  let e := prodBits (listBits natBits) (prodBits natBits natBits)
  let rows := Poly.fst (listBits natBits) (prodBits natBits natBits)
  let x := Poly.snd (listBits natBits) (prodBits natBits natBits)
  let v := x.comp (Poly.fst natBits natBits)
  let port := x.comp (Poly.snd natBits natBits)
  let base := ((Poly.const e natBits q).pair v).comp Poly.natMul
  let idx := (port.pair base).comp Poly.natAdd
  let r := (idx.pair rows).comp (Poly.listGetD natBits 0)
  let qp := r.pair (Poly.const e natBits q)
  exact ((qp.comp Poly.natDiv).pair (qp.comp Poly.natMod)).congr (fun _ => by
    simp only [Function.comp_apply,lookup,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD])

 theorem lookup_erase {q v : ℕ} (T : ExpanderTables.Table v q) (x : Fin v × Fin q) :
    lookup q (T.rows.toList.map Fin.val,(x.1.val,x.2.val)) =
      ((ExpanderTables.lookup T x).1.val,(ExpanderTables.lookup T x).2.val) := by
  have hi : x.2.val+q*x.1.val < (T.rows.toList.map Fin.val).length := by
    simp only [List.length_map,Vector.length_toList]
    exact (ExpanderTables.rowIndex v q x).isLt
  rw [lookup,List.getD_eq_getElem _ _ hi,List.getElem_map]
  rfl

def stepRow (d : ℕ) (H : List ℕ) (p : Data × ℕ) : ℕ :=
  let D := d*d
  let g := D*D
  let x := p.2/D
  let port := p.2%D
  let first := lookup d (H,(x%g,port/d))
  let outerFirst := lookup D (p.1.2,(x/g,first.1/D))
  let outerSecond := lookup D (p.1.2,(outerFirst.1,first.1%D))
  let last := lookup d (H,(outerFirst.2+D*outerSecond.2,port%d))
  (first.2+d*last.2)+D*(last.1+g*outerSecond.1)

def stepData (d : ℕ) (H : List ℕ) (T : Data) : Data :=
  let v := T.1*((d*d)*(d*d))
  (v,(List.range (v*(d*d))).map (fun i => stepRow d H (T,i)))

noncomputable def stepRowPoly (d : ℕ) (H : List ℕ) :
    Poly (prodBits dataCode natBits) natBits (stepRow d H) := by
  let e := prodBits dataCode natBits
  let D := d*d
  let g := D*D
  let c (n : ℕ) := Poly.const e natBits n
  let T := Poly.fst dataCode natBits
  let rows := T.comp (Poly.snd natBits (listBits natBits))
  let i := Poly.snd dataCode natBits
  let x := (i.pair (c D)).comp Poly.natDiv
  let port := (i.pair (c D)).comp Poly.natMod
  let Hc := Poly.const e (listBits natBits) H
  let first := (Hc.pair (((x.pair (c g)).comp Poly.natMod).pair
    ((port.pair (c d)).comp Poly.natDiv))).comp (lookupPoly d)
  let firstV := first.comp (Poly.fst natBits natBits)
  let firstP := first.comp (Poly.snd natBits natBits)
  let out₁ := (rows.pair (((x.pair (c g)).comp Poly.natDiv).pair
    ((firstV.pair (c D)).comp Poly.natDiv))).comp (lookupPoly D)
  let out₁V := out₁.comp (Poly.fst natBits natBits)
  let out₁P := out₁.comp (Poly.snd natBits natBits)
  let out₂ := (rows.pair (out₁V.pair ((firstV.pair (c D)).comp Poly.natMod))).comp (lookupPoly D)
  let out₂V := out₂.comp (Poly.fst natBits natBits)
  let out₂P := out₂.comp (Poly.snd natBits natBits)
  let lastV := (out₁P.pair (((c D).pair out₂P).comp Poly.natMul)).comp Poly.natAdd
  let last := (Hc.pair (lastV.pair ((port.pair (c d)).comp Poly.natMod))).comp (lookupPoly d)
  let v := ((last.comp (Poly.fst natBits natBits)).pair
    (((c g).pair out₂V).comp Poly.natMul)).comp Poly.natAdd
  let p := (firstP.pair (((c d).pair (last.comp (Poly.snd natBits natBits))).comp Poly.natMul)).comp Poly.natAdd
  exact (p.pair (((c D).pair v).comp Poly.natMul)).comp Poly.natAdd

noncomputable def stepDataPoly (d : ℕ) (H : List ℕ) : Poly dataCode dataCode (stepData d H) := by
  let v := ((Poly.fst natBits (listBits natBits)).pair
    (Poly.const dataCode natBits ((d*d)*(d*d)))).comp Poly.natMul
  let len := (v.pair (Poly.const dataCode natBits (d*d))).comp Poly.natMul
  exact v.pair (Poly.tabulate dataCode natBits (0,[]) 0 len (stepRowPoly d H))

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
