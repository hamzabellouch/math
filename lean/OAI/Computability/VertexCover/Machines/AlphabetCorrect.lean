import Mathlib
import OAI.Computability.VertexCover.Machines.FinCode
import OAI.Computability.VertexCover.Machines.AlphabetRow

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

 theorem old_valid {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) :
    old (T,e.val) = GenericMachine.rowData T.rows[e] := GenericMachine.lookup_valid T e
 theorem head_valid {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) :
    head (T,e.val) = T.rows[T.rows[e].reverseIndex].tail.val := by
  unfold head
  rw [old_valid]
  exact congrArg (fun r : GenericMachine.Row q => r.1.1)
    (GenericMachine.lookup_valid T T.rows[e].reverseIndex)

 theorem local_source {q : ℕ} (T : GenericGraphTables.Table q) (e : Fin T.darts) (l : Local q) :
    localRow l (T,e.val) = TableMachine.rowData (Table.rowFromDart T (((e,l.1.1),l.1.2),l.2)) := by
  rcases l with ⟨⟨event,slot⟩,b⟩
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [localRow,TableMachine.rowData,Table.rowFromDart]
      cases b with
      | false => simp only [Bool.false_eq_true,ite_false,vertexEquiv_event_val,eventEquiv_val]
      | true =>
        simp only [ite_true]
        unfold queryRank
        rw [old_valid]
        dsimp only [GenericMachine.rowData]
        cases h : Queries.query (GenericGraphTables.relationAt T.rows[e].relation) event slot with
        | inl z =>
          rcases z with ⟨side,tape⟩
          simp only [Queries.globalize,vertexEquiv_vertexAddress_val]
          cases side <;> simp [eventCount,head_valid]
        | inr tape =>
          simp only [Queries.globalize,vertexEquiv_edgeAddress_val,eventCount]
    · change e.val*blockCount q+(blockEquiv q ((event,slot),!b)).val =
        (dartEquiv T.darts q (((e,event),slot),!b)).val
      rw [dart_block_val e ((event,slot),!b)]
      ring
  · dsimp only [localRow,TableMachine.rowData,Table.rowFromDart]
    rw [old_valid,head_valid]
    simp only [GenericMachine.rowData,Fin.ext_iff]
    rfl

def row {q : ℕ} (s : State q) : TableMachine.Row :=
  localRow ((blockEquiv q).symm ⟨s.2%blockCount q,Nat.mod_lt _ (block_pos q)⟩)
    (s.1,s.2/blockCount q)
noncomputable def rowPoly {q : ℕ} : Poly (code (q := q)) TableMachine.rowCode row := by
  let t : Poly (code (q := q)) GenericMachine.code Prod.fst := tablePoly
  let i : Poly (code (q := q)) natBits Prod.snd := indexPoly
  let e := (i.pair (Poly.const _ natBits (blockCount q))).comp Poly.natDiv
  let j := i.comp (Poly.finMod (blockCount q) (block_pos q))
  letI : Nonempty (Fin (blockCount q)) := ⟨⟨0,block_pos q⟩⟩
  exact ((t.pair e).pair j).comp (Poly.finiteBranch code finCode TableMachine.rowCode
    (finCode_injective _) (fun s k => localRow ((blockEquiv q).symm k) s)
    (fun k => localPoly _))

 theorem row_source {q : ℕ} (T : GenericGraphTables.Table q) (i : Fin (Table.build T).darts) :
    row (T,i.val) = TableMachine.rowData (Table.build T).rows[i] := by
  obtain ⟨⟨⟨⟨e,event⟩,slot⟩,b⟩,rfl⟩ := (dartEquiv T.darts q).surjective i
  let l : Local q := ((event,slot),b)
  have he : (dartEquiv T.darts q (((e,event),slot),b)).val/blockCount q = e.val := by
    rw [dart_block_val e l,Nat.add_mul_div_left _ _ (block_pos q),Nat.div_eq_of_lt (blockEquiv q l).isLt,Nat.zero_add]
  have hj : (⟨(dartEquiv T.darts q (((e,event),slot),b)).val%blockCount q,Nat.mod_lt _ (block_pos q)⟩ : Fin (blockCount q)) = blockEquiv q l := by
    apply Fin.ext
    change (dartEquiv T.darts q (((e,event),slot),b)).val%blockCount q = (blockEquiv q l).val
    rw [dart_block_val e l,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (blockEquiv q l).isLt]
  unfold row
  conv_lhs => rw [he,hj,Equiv.symm_apply_apply]
  change localRow l (T,e.val) = TableMachine.rowData (Table.rows T)[dartEquiv T.darts q (((e,event),slot),b)]
  rw [Table.rows_at,Equiv.symm_apply_apply]
  exact local_source T e l

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
