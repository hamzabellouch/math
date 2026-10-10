import Mathlib
import OAI.Computability.VertexCover.Machines.ListFilter
import OAI.Computability.VertexCover.Machines.GraphDescriptor
import OAI.Computability.VertexCover.Machines.NumberedGraph

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
noncomputable section
variable {a b d : ℕ}
def weightCount (a b d : ℕ) : ℕ := Fintype.card (Weight a b d)
theorem weightCount_pos : 0<weightCount a b d :=
  Fintype.card_pos_iff.mpr ⟨defaultWeight⟩
def count (I : FixedLC a b) (d : ℕ) : ℕ := I.M ^ Fintype.card (PositionPair d) * weightCount a b d
theorem count_pos (I : FixedLC a b) (d : ℕ) : 0<count I d :=
  Nat.mul_pos (pow_pos I.Mpos _) weightCount_pos

def seedEquiv (I : FixedLC a b) (d : ℕ) : Fin (I.M ^ Fintype.card (PositionPair d)) ≃ I.toLC.Seeds d :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Fintype.equivFin (PositionPair d)).symm (Equiv.refl _))
theorem seedEquiv_apply (I : FixedLC a b) (n : Fin (I.M ^ Fintype.card (PositionPair d))) :
    seedEquiv I d n=seed I n.val := by
  rfl

def numberEquiv (I : FixedLC a b) (d : ℕ) : Fin (count I d) ≃ I.toLC.Vertex d :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (seedEquiv I d) (Fintype.equivFin (Weight a b d)).symm)
def decode (n : ℕ) : RawVertex a b d :=
  (n / weightCount a b d, (Fintype.equivFin (Weight a b d)).symm ⟨n % weightCount a b d,Nat.mod_lt _ weightCount_pos⟩)
theorem numberEquiv_apply (I : FixedLC a b) (n : Fin (count I d)) :
    numberEquiv I d n=rawVertex I (decode n.val) := rfl

def fullEquiv (I : FixedLC a b) (d : ℕ) : Fin (count I d) ≃ I.toLC.Vertex d :=
  (numberEquiv I d).trans (I.toLC.profileVertexEquiv d)
def graph (I : FixedLC a b) (d : ℕ) (t : ℝ) : SimpleGraph (Fin (count I d)) :=
  (I.toLC.graph d t).comap (fullEquiv I d)
def explicitGraph (I : FixedLC a b) (d : ℕ) (t : ℝ) : ExplicitGraph :=
  ExplicitGraph.numbered (graph I d t)

def countPoly (hb : 0<b) (d : ℕ) : Poly (FixedLC.code (a := a) (b := b)) natBits (fun I => count I d) :=
  ((((FixedLC.MPoly hb).comp (Poly.natPow (Fintype.card (PositionPair d)))).pair
    (Poly.const FixedLC.code natBits (weightCount a b d))).comp Poly.natMul).congr (fun _ => rfl)
def decodePoly : Poly natBits (vertexCode (a := a) (b := b) (d := d)) decode := by
  let q := ((Poly.identity natBits).pair (Poly.const natBits natBits (weightCount a b d))).comp Poly.natDiv
  let r := (Poly.finMod (weightCount a b d) weightCount_pos).comp
    (Poly.finite finCode weightCode (finCode_injective _) (Fintype.equivFin (Weight a b d)).symm)
  exact (q.pair r).congr (fun _ => rfl)

def numberFrame (p : FixedLC a b × (ℕ × ℕ)) : Frame a b d :=
  (p.1,(decode p.2.1,decode p.2.2))
def numberFramePoly : Poly (prodBits (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits))
    (frameCode (a := a) (b := b) (d := d)) numberFrame := by
  let I := Poly.fst (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)
  let p := Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)
  exact I.pair (((p.comp (Poly.fst natBits natBits)).comp decodePoly).pair
    ((p.comp (Poly.snd natBits natBits)).comp decodePoly))

def test (t : ℝ) (p : FixedLC a b × (ℕ × ℕ)) : Bool :=
  decide (p.2.1<p.2.2) && (descriptor (numberFrame (d := d) p)).test t

attribute [local irreducible] Descriptor.test

def normNumberPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  (numberFramePoly (a := a) (b := b) (d := d)).comp
    (normTestPoly (a := a) (b := b) (d := d) ha hb t)
def lessPoly (a b : ℕ) :=
  (Poly.snd (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)).comp Poly.natLt
def testPrePoly (ha : 0<a) (hb : 0<b) (t : ℝ) :=
  ((lessPoly a b).pair (normNumberPoly (d := d) ha hb t)).comp
    (Poly.bool₂ (fun p => p.1 && p.2))
def testPoly (ha : 0<a) (hb : 0<b) (t : ℝ) :
    Poly (prodBits (FixedLC.code (a := a) (b := b)) (prodBits natBits natBits)) boolBits (test (d := d) t) :=
  (testPrePoly (d := d) ha hb t).congr (fun _ => rfl)

theorem test_correct (I : FixedLC a b) (t : ℝ) (u v : Fin (count I d)) :
    test (d := d) t (I,(u.val,v.val))=true ↔ u<v ∧ (graph I d t).Adj u v := by
  classical
  simp only [test,Bool.and_eq_true,decide_eq_true_iff]
  rw [normTest_correct]
  change (u.val<v.val ∧ _) ↔ (u<v ∧ fullEquiv I d u ≠ fullEquiv I d v ∧ _)
  have he (n : Fin (count I d)) : fullEquiv I d n=I.toLC.profileVertexEquiv d (rawVertex I (decode n.val)) := rfl
  simp only [he,numberFrame]
  constructor
  · rintro ⟨hl,hn⟩
    exact ⟨hl,fun h => (ne_of_lt hl) (congrArg Fin.val ((fullEquiv I d).injective h)),hn⟩
  · rintro ⟨hl,_,hn⟩; exact ⟨hl,hn⟩
end
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
