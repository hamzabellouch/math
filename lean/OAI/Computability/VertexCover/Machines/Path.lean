import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringTest
import OAI.Computability.VertexCover.Machines.Address

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

namespace VertexCover.Machine.PathMachine
open UniqueGames.Foundations.PCP
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach WalkMachine

noncomputable def edgeTestPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) (k : Fin (n+1)) :
    Poly (code (d := d)) boolBits (fun s =>
      PortTables.accepts s.1.2 (edgeAt (PortTables.portGraph s.1.2) n (s.2,p) k)
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1) s.2) a
          (tailFromStart (PortTables.portGraph s.1.2) n (s.2,p) k))
        (decode (finitePortSelector (PortTables.portGraph s.1.2) (n+1)
          (endpoint (PortTables.portGraph s.1.2) (s.2,p))) b
          (headFromEnd (PortTables.portGraph s.1.2) n (s.2,p) k))) := by
  let es := edgePoly n p k
  let ts := es.comp (Poly.fst code finCode)
  let hs := es.comp (stepVariablePoly hd)
  let al := (((Poly.identity code).pair (ts.comp vertexPoly)).comp (AddressMachine.searchPoly (n+1) a))
  let bl := (((wordPoly (n+1) p).pair (hs.comp vertexPoly)).comp (AddressMachine.searchPoly (n+1) b))
  let pr := es.comp (Poly.snd code finCode)
  let result := (ts.pair (pr.pair (al.pair bl))).comp (acceptsVariablePoly hd)
  exact result.congr (fun s => by
    rcases s with ⟨T,v⟩
    exact congrArg₂ (PortTables.accepts T.2 (edgeAt (PortTables.portGraph T.2) n (v,p) k))
      (AddressMachine.search_decode T (n+1) v
        (tailFromStart (PortTables.portGraph T.2) n (v,p) k) a)
      (AddressMachine.search_decode T (n+1) (endpoint (PortTables.portGraph T.2) (v,p))
        (headFromEnd (PortTables.portGraph T.2) n (v,p) k) b))

noncomputable def pathPoly {d : ℕ} (hd : 0<d) (n : ℕ) (p : Fin (n+1) → Fin d)
    (a b : PaddedLabel (Fin d) (n+1) GraphTables.Label) :
    Poly (code (d := d)) boolBits (fun s =>
      PoweringTest.pathAccepts (PortTables.portGraph s.1.2) (PortTables.accepts s.1.2) n
        (finitePortSelector (PortTables.portGraph s.1.2) (n+1)) (s.2,p) a b) :=
  (Poly.finiteAll code _ (edgeTestPoly hd n p a b)).congr (fun _ => by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff,PoweringTest.pathAccepts_eq_true_iff])

end VertexCover.Machine.PathMachine
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
