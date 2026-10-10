import Mathlib
import OAI.Computability.VertexCover.Machines.TableBase
import OAI.Computability.VertexCover.Machines.FinCode

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

noncomputable def finiteCode (α : Type) [Fintype α] (a : α) : List Bool :=
  finCode (Fintype.equivFin α a)
theorem finiteCode_injective (α : Type) [Fintype α] : Function.Injective (finiteCode α) :=
  (finCode_injective _).comp (Fintype.equivFin α).injective

structure FixedLC (a b : ℕ) where
  u : ℕ
  v : ℕ
  M : ℕ
  apos : 0<a
  bpos : 0<b
  Mpos : 0<M
  left : Fin M → Fin u
  right : Fin M → Fin v
  projection : Fin M → Fin a → Fin b

namespace FixedLC
variable {a b : ℕ}
def toLC (I : FixedLC a b) : LabelCover where
  u := I.u
  v := I.v
  qU := a
  qV := b
  M := I.M
  qU_pos := I.apos
  qV_pos := I.bpos
  M_pos := I.Mpos
  left := I.left
  right := I.right
  projection := I.projection

def one (ha : 0<a) (hb : 0<b) : FixedLC a b where
  u := 1
  v := 1
  M := 1
  apos := ha
  bpos := hb
  Mpos := by decide
  left := fun _ => 0
  right := fun _ => 0
  projection := fun _ _ => ⟨0,hb⟩

abbrev Map (a b : ℕ) := Fin a → Fin b
abbrev Row (a b : ℕ) := (ℕ × ℕ) × Map a b
abbrev Data (a b : ℕ) := ℕ × (ℕ × List (Row a b))
noncomputable def mapCode : Map a b → List Bool := finiteCode (Map a b)
noncomputable def rowCode : Row a b → List Bool := prodBits (prodBits natBits natBits) mapCode
noncomputable def dataCode : Data a b → List Bool := prodBits natBits (prodBits natBits (listBits rowCode))
def data (I : FixedLC a b) : Data a b :=
  (I.u,(I.v,List.ofFn (fun e => ((I.left e |>.val,I.right e |>.val),I.projection e))))
noncomputable def code (I : FixedLC a b) : List Bool := dataCode I.data
def rowDefault (hb : 0<b) : Row a b := ((0,0),fun _ => ⟨0,hb⟩)
noncomputable def uPoly : Poly (code (a := a) (b := b)) natBits FixedLC.u :=
  (Poly.fst natBits (prodBits natBits (listBits rowCode))).encodeCongr data (fun _ => rfl) (fun _ => rfl)
noncomputable def restPoly : Poly (code (a := a) (b := b)) (prodBits natBits (listBits rowCode))
    (fun I => I.data.2) :=
  (Poly.snd natBits (prodBits natBits (listBits rowCode))).encodeCongr data (fun _ => rfl) (fun _ => rfl)
noncomputable def vPoly : Poly (code (a := a) (b := b)) natBits FixedLC.v :=
  restPoly.comp (Poly.fst natBits (listBits rowCode))
noncomputable def rowsPoly : Poly (code (a := a) (b := b)) (listBits rowCode) (fun I => I.data.2.2) :=
  restPoly.comp (Poly.snd natBits (listBits rowCode))
noncomputable def MPoly (hb : 0<b) : Poly (code (a := a) (b := b)) natBits FixedLC.M :=
  (rowsPoly.comp (Poly.listLength rowCode (rowDefault hb))).congr (fun I => by simp [data])
def lookup (hb : 0<b) (p : FixedLC a b × ℕ) : Row a b := p.1.data.2.2.getD p.2 (rowDefault hb)
noncomputable def lookupPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) rowCode (lookup hb) :=
  (((Poly.snd code natBits).pair ((Poly.fst code natBits).comp rowsPoly)).comp
    (Poly.listGetD rowCode (rowDefault hb))).congr (fun _ => by
      simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop]
      rfl)
 theorem lookup_valid (hb : 0<b) (I : FixedLC a b) (e : Fin I.M) :
    lookup hb (I,e.val) = ((I.left e |>.val,I.right e |>.val),I.projection e) := by
  simp only [lookup,data,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp
noncomputable def leftPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) natBits (fun p => (lookup hb p).1.1) :=
  (lookupPoly hb).comp ((Poly.fst (prodBits natBits natBits) mapCode).comp (Poly.fst natBits natBits))
noncomputable def rightPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) natBits (fun p => (lookup hb p).1.2) :=
  (lookupPoly hb).comp ((Poly.fst (prodBits natBits natBits) mapCode).comp (Poly.snd natBits natBits))
noncomputable def relationPoly (hb : 0<b) :
    Poly (prodBits (code (a := a) (b := b)) natBits) mapCode (fun p => (lookup hb p).2) :=
  (lookupPoly hb).comp (Poly.snd (prodBits natBits natBits) mapCode)

noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α)
    (Q : α → FixedLC a b) (hb : 0<b) {r : α × ℕ → Row a b}
    (cu : Poly ea natBits (fun x => (Q x).u))
    (cv : Poly ea natBits (fun x => (Q x).v))
    (cm : Poly ea natBits (fun x => (Q x).M))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ x (e : Fin (Q x).M), r (x,e.val) = (((Q x).left e |>.val,(Q x).right e |>.val),(Q x).projection e)) :
    Poly ea code Q := by
  let rows := Poly.tabulate ea rowCode a₀ (rowDefault hb) cm cr
  have he (x : α) : (List.range (Q x).M).map (fun e => r (x,e)) = (Q x).data.2.2 := by
    apply List.ext_getElem
    · simp [data]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,data,List.getElem_ofFn]
      exact hr x ⟨i,by simpa using hi⟩
  exact (cu.pair (cv.pair rows)).encodeCongr id (fun _ => rfl) (fun x => by
    change dataCode ((Q x).u,((Q x).v,_)) = dataCode (data (Q x))
    rw [he]
    rfl)
end FixedLC
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
