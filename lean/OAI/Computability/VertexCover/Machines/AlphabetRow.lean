import Mathlib
import OAI.Computability.VertexCover.Machines.Codec
import OAI.Computability.VertexCover.Machines.AlphabetFrame

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

namespace VertexCover.Machine.AlphabetMachine
open UniqueGames.Foundations.PCP
open AlphabetTable Enumeration

def queryRank {q : ℕ} (s : State q) : Queries.RawQuery q → ℕ
  | .inl (side,tape) => (if side then head s else (old s).1.1)*tapeCount q+(cubeEquiv q tape).val
  | .inr tape => s.1.vertices*tapeCount q + (s.2*pairTapeCount q+(pairCubeEquiv q tape).val)
noncomputable def queryRankPoly {q : ℕ} (r : Queries.RawQuery q) :
    Poly (code (q := q)) natBits (fun s => queryRank s r) := by
  cases r with
  | inl p =>
    let endpoint : Poly (code (q := q)) natBits (fun s => if p.1 then head s else (old s).1.1) :=
      if h : p.1 then headPoly.congr (by intro s; simp [h])
      else tailPoly.congr (by intro s; simp [h])
    exact (((endpoint.pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul).pair
      (Poly.const _ natBits (cubeEquiv q p.2).val)).comp Poly.natAdd
  | inr tape =>
    let v := ((verticesPoly (q := q)).pair (Poly.const _ natBits (tapeCount q))).comp Poly.natMul
    let e := ((indexPoly (q := q)).pair (Poly.const _ natBits (pairTapeCount q))).comp Poly.natMul
    exact (v.pair ((e.pair (Poly.const _ natBits (pairCubeEquiv q tape).val)).comp Poly.natAdd)).comp Poly.natAdd
noncomputable def queryPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s =>
      queryRank s (Queries.query (GenericGraphTables.relationAt (old s).2) l.1.1 l.1.2)) := by
  letI := relationFintype q
  letI : Nonempty (GenericGraphTables.RelationTable q) := ⟨GenericMachine.relationDefault q⟩
  exact (((Poly.identity (code (q := q))).pair relationPoly).comp
    (Poly.finiteBranch code GenericMachine.relationCode natBits (relationCode_injective q)
      (fun s r => queryRank s (Queries.query (GenericGraphTables.relationAt r) l.1.1 l.1.2))
      (fun r => queryRankPoly _))).congr (fun _ => rfl)

def localRow {q : ℕ} (l : Local q) (s : State q) : TableMachine.Row :=
  ((if l.2 then s.1.darts*localCount q +
      queryRank s (Queries.query (GenericGraphTables.relationAt (old s).2) l.1.1 l.1.2)
    else s.2*localCount q+(localEventEquiv q l.1.1).val,
    s.2*blockCount q+(blockEquiv q (l.1,!l.2)).val),
    Relations.relationFromTable (old s).2 (decide ((old s).1.1=head s)) l.1.1 l.1.2 l.2)
noncomputable def localTailPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s => (localRow l s).1.1) := by
  if h : l.2 then
    let count := ((dartsPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
    exact ((count.pair (queryPoly l)).comp Poly.natAdd).congr (by intro s; simp [localRow,h])
  else
    let offset := ((indexPoly (q := q)).pair (Poly.const _ natBits (localCount q))).comp Poly.natMul
    exact ((offset.pair (Poly.const _ natBits (localEventEquiv q l.1.1).val)).comp Poly.natAdd).congr
      (by intro s; simp [localRow,h])
noncomputable def localReversePoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) natBits (fun s => (localRow l s).1.2) :=
  ((((indexPoly (q := q)).pair (Poly.const _ natBits (blockCount q))).comp Poly.natMul).pair
    (Poly.const _ natBits (blockEquiv q (l.1,!l.2)).val)).comp Poly.natAdd
noncomputable def localRelationPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) TableMachine.relationCode (fun s => (localRow l s).2) := by
  letI := relationFintype q
  exact (relationPoly.pair loopPoly).comp (Poly.finite
    (prodBits GenericMachine.relationCode boolBits) TableMachine.relationCode
    (prodBits_injective (relationCode_injective q) boolBits_injective)
    (fun p => Relations.relationFromTable p.1 p.2 l.1.1 l.1.2 l.2))
noncomputable def localPoly {q : ℕ} (l : Local q) :
    Poly (code (q := q)) TableMachine.rowCode (localRow l) :=
  ((localTailPoly l).pair (localReversePoly l)).pair (localRelationPoly l)

end VertexCover.Machine.AlphabetMachine
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
