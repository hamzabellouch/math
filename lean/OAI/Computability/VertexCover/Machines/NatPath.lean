import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringTest
import OAI.Computability.VertexCover.Machines.Address
import OAI.Computability.VertexCover.Machines.NatWalk

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

namespace VertexCover.Machine.NatPathMachine
open UniqueGames.Foundations.PCP
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach NatWalkMachine

def search {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (x : State d × ℕ) : GraphTables.Label :=
  FixedSearch.run (fun x w => decide ((word w.1.val w.2 x.1).2=x.2))
    (fun _ w => a w) 0 (allAddresses d t) x
noncomputable def searchPoly {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label) :
    Poly (prodBits (code (d := d)) natBits) finCode (search t a) :=
  FixedSearch.poly (prodBits code natBits) finCode _ _ 0
    (fun w => ((((Poly.fst code natBits).comp (wordPoly w.1.val w.2)).comp
      (Poly.snd PortMachine.code natBits)).pair (Poly.snd code natBits)).comp Poly.natEq)
    (fun w => Poly.const _ finCode (a w)) (allAddresses d t)
 theorem search_forget {d : ℕ} (t : ℕ) (a : PaddedLabel (Fin d) t GraphTables.Label)
    (s : WalkMachine.State d) (u : ℕ) :
    search t a (forget s,u) = AddressMachine.search t a (s,u) := by
  unfold search AddressMachine.search
  generalize allAddresses d t = xs
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    dsimp only [FixedSearch.run]
    exact if_congr (Iff.of_eq (congrArg (fun x : State d => decide (x.2=u)=true)
      (word_forget w.1.val w.2 s))) rfl ih

def edgeTest {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) (s : State d) : Bool :=
  let e := edge n p k s
  accepts e.2 (search (n+1) a (s,e.1.2))
    (search (n+1) b (word (n+1) p s,(step e.2 e.1).2)) e.1
noncomputable def edgeTestPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) :
    Poly (code (d := d)) boolBits (edgeTest n p a b k) := by
  let es := edgePoly n p k
  let ts := es.comp (Poly.fst code finCode)
  let hs := es.comp (stepVariablePoly hd)
  let al := (((Poly.identity code).pair (ts.comp (Poly.snd PortMachine.code natBits))).comp (searchPoly (n+1) a))
  let bl := (((wordPoly (n+1) p).pair (hs.comp (Poly.snd PortMachine.code natBits))).comp (searchPoly (n+1) b))
  let pr := es.comp (Poly.snd code finCode)
  exact (ts.pair (pr.pair (al.pair bl))).comp (acceptsVariablePoly hd)

 theorem edgeTest_source {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) (s : WalkMachine.State d) :
    edgeTest n p a b k (forget s) =
      PortTables.accepts s.1.2 (edgeAt (PortTables.portGraph s.1.2) n (s.2,p) k)
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1) s.2) a
          (tailFromStart (PortTables.portGraph s.1.2) n (s.2,p) k))
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1)
          (endpoint (PortTables.portGraph s.1.2) (s.2,p))) b
          (headFromEnd (PortTables.portGraph s.1.2) n (s.2,p) k)) := by
  simp only [edgeTest,edge_forget,step_forget,word_forget,search_forget,accepts_forget]
  rcases s with ⟨T,v⟩
  exact congrArg₂ (PortTables.accepts T.2 (edgeAt (PortTables.portGraph T.2) n (v,p) k))
    (AddressMachine.search_decode T (n+1) v
      (tailFromStart (PortTables.portGraph T.2) n (v,p) k) a)
    (AddressMachine.search_decode T (n+1) (endpoint (PortTables.portGraph T.2) (v,p))
      (headFromEnd (PortTables.portGraph T.2) n (v,p) k) b)

def path {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (s : State d) : Bool :=
  decide (∀ k, edgeTest n p a b k s=true)
noncomputable def pathPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) :
    Poly (code (d := d)) boolBits (path n p a b) :=
  (Poly.finiteAll code _ (edgeTestPoly hd n p a b)).congr (fun _ => by
    apply Bool.eq_iff_iff.mpr
    simp only [path,decide_eq_true_iff])
 theorem path_source {d : ℕ} (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (s : WalkMachine.State d) :
    path n p a b (forget s) = PoweringTest.pathAccepts (PortTables.portGraph s.1.2)
      (PortTables.accepts s.1.2) n (finitePortSelector (PortTables.portGraph s.1.2) (n+1)) (s.2,p) a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [path,decide_eq_true_iff,PoweringTest.pathAccepts_eq_true_iff,edgeTest_source]

end VertexCover.Machine.NatPathMachine
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
