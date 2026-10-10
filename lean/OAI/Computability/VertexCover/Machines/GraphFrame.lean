import Mathlib
import OAI.Computability.VertexCover.Machines.ListSearch
import OAI.Computability.VertexCover.Machines.ListFilter
import OAI.Computability.VertexCover.Machines.Codec
import OAI.Computability.VertexCover.Machines.FixedOps
import OAI.Computability.VertexCover.Machines.LCData
import OAI.Computability.VertexCover.Machines.DescriptorMath

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
 theorem foldl_and_all (xs : List Bool) (b : Bool) : xs.foldl (· && ·) b=(b && xs.all id) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih,Bool.and_assoc]
noncomputable def Poly.boundAll {α : Type} (ea : α → List Bool) (a₀ : α)
    {n : α → ℕ} {f : α × ℕ → Bool} (cn : Poly ea natBits n)
    (cf : Poly (prodBits ea natBits) boolBits f) :
    Poly ea boolBits (fun a => decide (∀ i, i<n a → f (a,i)=true)) :=
  ((Poly.tabulate ea boolBits a₀ false cn cf).comp Poly.listAnd).congr (fun a => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,foldl_and_all,Bool.true_and,List.all_eq_true,List.mem_map,
      List.mem_range,decide_eq_true_iff]
    constructor
    · intro h i hi; exact h _ ⟨i,hi,rfl⟩
    · rintro h b ⟨i,hi,rfl⟩; exact h i hi)
noncomputable def Poly.decideAnd {α : Type} (ea : α → List Bool)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (cp : Poly ea boolBits (fun a => decide (P a)))
    (cq : Poly ea boolBits (fun a => decide (Q a))) :
    Poly ea boolBits (fun a => decide (P a ∧ Q a)) :=
  ((cp.pair cq).comp (Poly.bool₂ (fun p => p.1 && p.2))).congr (fun a => by simp)
noncomputable def Poly.decideForall {α ι : Type} [Fintype ι] (ea : α → List Bool)
    (P : α → ι → Prop) [∀ a, DecidablePred (P a)]
    (cp : ∀ i, Poly ea boolBits (fun a => decide (P a i))) :
    Poly ea boolBits (fun a => decide (∀ i, P a i)) :=
  (Poly.finiteAll ea (fun a i => decide (P a i)) cp).congr (fun a => by simp)
noncomputable def Poly.natEqual : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1=p.2)) := Poly.natEq.congr (fun _ => rfl)

namespace GraphMachine
open LabelCover
variable {a b d : ℕ}
abbrev Weight (a b d : ℕ) := Fin d → Fin ((max a b)^(d-1)) → Fin (2*d+1)
abbrev RawVertex (a b d : ℕ) := ℕ × Weight a b d
abbrev Frame (a b d : ℕ) := FixedLC a b × (RawVertex a b d × RawVertex a b d)
noncomputable def weightCode : Weight a b d → List Bool := finiteCode _
noncomputable def vertexCode : RawVertex a b d → List Bool := prodBits natBits weightCode
noncomputable def frameCode : Frame a b d → List Bool := prodBits FixedLC.code (prodBits vertexCode vertexCode)
def defaultWeight : Weight a b d := fun _ _ => ⟨0,by omega⟩
def defaultFrame (ha : 0<a) (hb : 0<b) : Frame a b d :=
  (FixedLC.one ha hb,((0,defaultWeight),(0,defaultWeight)))
noncomputable def seed (I : FixedLC a b) (n : ℕ) : I.toLC.Seeds d :=
  fun e => ⟨n/I.M^(Fintype.equivFin (PositionPair d) e).val%I.M,Nat.mod_lt _ I.Mpos⟩
def vertexAt (p : Frame a b d) (x : Bool) : RawVertex a b d := if x then p.2.2 else p.2.1
noncomputable abbrev Q (p : Frame a b d) (x : TracePos d) : p.1.toLC.Query d :=
  p.1.toLC.query (seed p.1 (vertexAt p x.1).1) x.2
def W (p : Frame a b d) : TraceWeights a b d := fun x => (vertexAt p x.1).2 x.2
noncomputable def rawVertex (I : FixedLC a b) (v : RawVertex a b d) : I.toLC.Vertex d :=
  (seed I v.1,v.2)
noncomputable def descriptor (p : Frame a b d) : Descriptor a b d := diagram (Q p) (W p)
noncomputable def instancePoly : Poly (frameCode (a := a) (b := b) (d := d)) FixedLC.code Prod.fst :=
  Poly.fst FixedLC.code (prodBits vertexCode vertexCode)
noncomputable def atPoly (x : Bool) : Poly (frameCode (a := a) (b := b) (d := d)) vertexCode (fun p => vertexAt p x) := by
  let c := Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits (vertexCode (a := a) (b := b) (d := d)) (vertexCode (a := a) (b := b) (d := d)))
  cases x
  · exact (c.comp (Poly.fst vertexCode vertexCode)).congr (fun _ => rfl)
  · exact (c.comp (Poly.snd vertexCode vertexCode)).congr (fun _ => rfl)
noncomputable def seedNumberPoly (x : Bool) : Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => (vertexAt p x).1) :=
  (atPoly x).comp (Poly.fst natBits weightCode)
noncomputable def weightPoly : Poly (frameCode (a := a) (b := b) (d := d)) (finiteCode (TraceWeights a b d)) W := by
  let c := ((atPoly (a := a) (b := b) (d := d) false).comp (Poly.snd natBits weightCode)).pair ((atPoly true).comp (Poly.snd natBits weightCode))
  exact (c.comp (Poly.finite _ _ (prodBits_injective (finiteCode_injective _) (finiteCode_injective _))
    (fun p : Weight a b d × Weight a b d => fun x : TracePos d => (if x.1 then p.2 else p.1) x.2))).congr
      (fun p => by funext x; rcases x with ⟨x,j⟩; cases x <;> rfl)
noncomputable def samplePoly (hb : 0<b) (x : Bool) (e : PositionPair d) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits
      (fun p => (seed p.1 (vertexAt p x).1 e).val) := by
  let cm := (instancePoly (a := a) (b := b) (d := d)).comp (FixedLC.MPoly hb)
  exact ((((seedNumberPoly x).pair (cm.comp (Poly.natPow (Fintype.equivFin (PositionPair d) e).val))).comp
    Poly.natDiv).pair cm |>.comp Poly.natMod)
noncomputable def questionUPoly (hb : 0<b) (x : TracePos d) (k : {k : Fin d // x.2 < k}) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => ((Q p x).2.1 k).val) :=
  ((instancePoly.pair (samplePoly hb x.1 ⟨(x.2,k.val),k.property⟩)).comp (FixedLC.leftPoly hb)).congr
    (fun p => congrArg (fun r : FixedLC.Row a b => r.1.1)
      (FixedLC.lookup_valid hb p.1 (seed p.1 (vertexAt p x.1).1 ⟨(x.2,k.val),k.property⟩)))
noncomputable def questionVPoly (hb : 0<b) (x : TracePos d) (k : {k : Fin d // k < x.2}) :
    Poly (frameCode (a := a) (b := b) (d := d)) natBits (fun p => ((Q p x).2.2 k).val) :=
  ((instancePoly.pair (samplePoly hb x.1 ⟨(k.val,x.2),k.property⟩)).comp (FixedLC.rightPoly hb)).congr
    (fun p => congrArg (fun r : FixedLC.Row a b => r.1.2)
      (FixedLC.lookup_valid hb p.1 (seed p.1 (vertexAt p x.1).1 ⟨(k.val,x.2),k.property⟩)))
end GraphMachine
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
