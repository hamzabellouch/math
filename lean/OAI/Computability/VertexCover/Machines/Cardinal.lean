import Mathlib
import OAI.Computability.VertexCover.Machines.Option
import OAI.Computability.VertexCover.Machines.BoundedBinary
import OAI.Computability.VertexCover.Machines.ParseName
import OAI.Computability.VertexCover.Machines.ParseSize

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
open UniqueGames.BinaryEncoding

def firstName (bs : List Bool) : ℕ := ((parseName bs).getD (0,[])).1

noncomputable def firstNamePoly : Poly id Nat.bits firstName :=
  (NameParser.poly.comp (Poly.getD (prodBits Nat.bits id) (0,[]))).comp (Poly.fst Nat.bits id)

noncomputable def boundedFirstNamePoly : Poly id natBits (fun bs => min bs.length (firstName bs)) := by
  let digits : Poly id id (fun bs => (firstName bs).bits) :=
    firstNamePoly.encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact ((FormulaParser.rawLength.pair digits).comp Poly.decodeBounded).congr (fun bs => by
    simp only [Function.comp_apply,bitsValue_bits])

theorem firstName_encoded (n : ℕ) (rest : List Bool) :
    firstName (nameBits n++rest) = n := by simp [firstName]

theorem names_length (ns : List ℕ) : ns.length ≤ (ns.flatMap nameBits).length := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,nameBits_length]
    omega

theorem firstName_graph (G : ExplicitGraph) : firstName G.bits = G.n := by
  simp only [ExplicitGraph.bits,List.singleton_append]
  exact firstName_encoded _ _

theorem graph_card_le_bits (G : ExplicitGraph) : G.n ≤ G.bits.length := by
  have h := names_length ([G.n] ++ List.range G.n ++ [G.edges.length] ++
    G.edges.flatMap (fun e => [e.1.val,e.2.val]))
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_range] at h
  exact (by omega : G.n ≤ 1+G.n+1+(G.edges.flatMap (fun e => [e.1.val,e.2.val])).length).trans h

noncomputable def Poly.graphCard : Poly ExplicitGraph.bits natBits (fun G => G.n) :=
  boundedFirstNamePoly.encodeCongr ExplicitGraph.bits (fun _ => rfl) (fun G => by
    rw [firstName_graph,Nat.min_eq_right (graph_card_le_bits G)])

theorem firstName_list (xs : List ℕ) : firstName (natListBits xs) = xs.length := by
  exact firstName_encoded _ _

theorem natList_length_le_bits (xs : List ℕ) : xs.length ≤ (natListBits xs).length := by
  exact (Nat.le_succ _).trans (names_length (xs.length::xs))

noncomputable def Poly.natListCard : Poly natListBits natBits (List.length : List ℕ → ℕ) :=
  boundedFirstNamePoly.encodeCongr natListBits (fun _ => rfl) (fun xs => by
    rw [firstName_list,Nat.min_eq_right (natList_length_le_bits xs)])

noncomputable def Poly.natLT : Poly (prodBits natBits natBits) boolBits
    (fun p : ℕ × ℕ => decide (p.1<p.2)) :=
  ((((Poly.fst natBits natBits).comp Poly.natSucc).pair (Poly.snd natBits natBits)).comp
    Poly.natLE).congr (fun p => by simp only [Function.comp_apply,Nat.succ_le_iff])

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
