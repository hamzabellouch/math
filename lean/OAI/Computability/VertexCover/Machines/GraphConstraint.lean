import Mathlib
import OAI.Computability.VertexCover.Machines.GraphFrame

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

namespace VertexCover.Machine.GraphMachine
open LabelCover
variable {a b d : ℕ}
attribute [local instance 0] Classical.propDecidable
noncomputable def eqUPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // y.2 < k}) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).2.1 k=(Q p y).2.1 l)) :=
  (((questionUPoly hb x k).pair (questionUPoly hb y l)).comp Poly.natEqual).congr
    (fun p => by simp only [Function.comp_apply,Fin.ext_iff])
noncomputable def eqVPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // k < x.2}) (l : {k : Fin d // k < y.2}) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide ((Q p x).2.2 k=(Q p y).2.2 l)) :=
  (((questionVPoly hb x k).pair (questionVPoly hb y l)).comp Poly.natEqual).congr
    (fun p => by simp only [Function.comp_apply,Fin.ext_iff])
noncomputable def impliesConst {α : Type} (ea : α → List Bool) (P : α → Prop)
    [DecidablePred P] (R : Prop) [Decidable R] (cp : Poly ea boolBits (fun p => decide (P p))) :
    Poly ea boolBits (fun p => decide (P p → R)) :=
  (cp.comp (Poly.bool (fun b => !b || decide R))).congr (fun p => by simp)
noncomputable def overlapUPoly (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ k : {k : Fin d // x.2 < k}, ∀ l : {k : Fin d // y.2 < k},
        (Q p x).2.1 k=(Q p y).2.1 l → A.1 k=B.1 l)) :=
  Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    ((eqUPoly hb x y k l).comp (Poly.bool (fun z => !z || decide (A.1 k=B.1 l)))).congr
      (fun _ => by simp)))
noncomputable def overlapVPoly (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ k : {k : Fin d // k < x.2}, ∀ l : {k : Fin d // k < y.2},
        (Q p x).2.2 k=(Q p y).2.2 l → A.2 k=B.2 l)) :=
  Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    ((eqVPoly hb x y k l).comp (Poly.bool (fun z => !z || decide (A.2 k=B.2 l)))).congr
      (fun _ => by simp)))
noncomputable def rowTest (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b)
    (p : Frame a b d × ℕ) : Bool :=
  decide ((FixedLC.lookup hb (p.1.1,p.2)).1.1=((Q p.1 x).2.1 k).val →
    (FixedLC.lookup hb (p.1.1,p.2)).1.2=((Q p.1 y).2.2 l).val →
    (FixedLC.lookup hb (p.1.1,p.2)).2 A=B)
noncomputable def rowTestPoly (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b) :
    Poly (prodBits (frameCode (a := a) (b := b) (d := d)) natBits) boolBits (rowTest hb x y k l A B) := by
  let p := Poly.fst (frameCode (a := a) (b := b) (d := d)) natBits
  let c := ((p.comp instancePoly).pair (Poly.snd frameCode natBits)).comp (FixedLC.lookupPoly hb)
  let cl := (((c.comp (Poly.fst (prodBits natBits natBits) FixedLC.mapCode)).comp (Poly.fst natBits natBits)).pair
    (p.comp (questionUPoly hb x k))).comp Poly.natEqual
  let cr := (((c.comp (Poly.fst (prodBits natBits natBits) FixedLC.mapCode)).comp (Poly.snd natBits natBits)).pair
    (p.comp (questionVPoly hb y l))).comp Poly.natEqual
  let cm := (c.comp (Poly.snd (prodBits natBits natBits) FixedLC.mapCode)).comp
    (Poly.finite FixedLC.mapCode boolBits (finiteCode_injective _) (fun f : Fin a → Fin b => decide (f A=B)))
  exact (((cl.pair cr).comp (Poly.bool₂ (fun p => p.1 && p.2))).pair cm |>.comp
    (Poly.bool₂ (fun p => !p.1 || p.2))).congr (fun p => by simp [rowTest,Bool.or_assoc])
noncomputable def crossAtomPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d)
    (k : {k : Fin d // x.2 < k}) (l : {k : Fin d // k < y.2}) (A : Fin a) (B : Fin b) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ c : Fin p.1.M, p.1.left c=(Q p x).2.1 k →
        p.1.right c=(Q p y).2.2 l → p.1.projection c A=B)) := by
  let c := Poly.boundAll frameCode (defaultFrame ha hb) (instancePoly.comp (FixedLC.MPoly hb))
    (rowTestPoly hb x y k l A B)
  exact c.congr (fun p => by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    constructor
    · intro h e
      have hh := h e.val e.isLt
      simp only [rowTest,FixedLC.lookup_valid,decide_eq_true_eq] at hh
      intro hl hr
      exact hh (congrArg Fin.val hl) (congrArg Fin.val hr)
    · intro h n hn
      have hh := h ⟨n,hn⟩
      simp only [rowTest,FixedLC.lookup_valid hb p.1 ⟨n,hn⟩,decide_eq_true_eq]
      intro hl hr
      exact hh (Fin.ext hl) (Fin.ext hr))
noncomputable def crossPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (∀ c : Fin p.1.M, ∀ k : {k : Fin d // x.2 < k}, ∀ l : {k : Fin d // k < y.2},
        p.1.left c=(Q p x).2.1 k → p.1.right c=(Q p y).2.2 l → p.1.projection c (A.1 k)=B.2 l)) := by
  exact (Poly.decideForall frameCode _ (fun k => Poly.decideForall frameCode _ (fun l =>
    crossAtomPoly ha hb x y k l (A.1 k) (B.2 l)))).congr (fun p => by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_iff]
      constructor
      · intro h c k l; exact h k l c
      · intro h k l c; exact h c k l)
noncomputable def pairPoly (ha : 0<a) (hb : 0<b) (x y : TracePos d) (A B : Query.Profile a b d) :
    Poly (frameCode (a := a) (b := b) (d := d)) boolBits
      (fun p => decide (Query.ProfilePair (Q p x) (Q p y) A B)) :=
  (Poly.decideAnd frameCode _ _ (overlapUPoly hb x y A B)
    (Poly.decideAnd frameCode _ _ (overlapVPoly hb x y A B) (crossPoly ha hb x y A B))).congr
      (fun _ => by apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_iff]; rfl)
end VertexCover.Machine.GraphMachine
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
