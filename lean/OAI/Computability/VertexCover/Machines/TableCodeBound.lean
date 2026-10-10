import Mathlib
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
 theorem listBits_length_le {α : Type} (e : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ a ∈ xs, (e a).length ≤ B) : (listBits e xs).length ≤ xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hh := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [listBits_cons_length,List.length_cons]
    nlinarith
namespace TableMachine
 theorem size_le_code (T : GraphTables.Table) : T.vertices+T.darts ≤ (tableCode T).length := by
  have h := list_length_le_bits rowCode (T.rows.toList.map rowData)
  simp only [List.length_map,Vector.length_toList] at h
  simp only [tableCode,dataCode,tableData,prodBits,pairBits_length,natBits_length]
  omega
 theorem rowLength_le {n m : ℕ} (r : GraphTables.DartRow n m) :
    (rowCode (rowData r)).length ≤ 4100*(n+m+1) := by
  have ht := r.tail.isLt
  have hr := r.reverseIndex.isLt
  simp only [rowCode,rowData,prodBits,pairBits_length,natBits_length,relationCode_length]
  omega
 theorem codeLength_le (T : GraphTables.Table) :
    (tableCode T).length ≤ 10000*(T.vertices+T.darts+1)^2 := by
  have h := listBits_length_le rowCode (T.rows.toList.map rowData) (4100*(T.vertices+T.darts+1)) (by
    intro a ha
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    exact rowLength_le r)
  simp only [List.length_map,Vector.length_toList] at h
  have hm : T.darts ≤ T.vertices+T.darts := Nat.le_add_left _ _
  have hp := Nat.mul_le_mul_right (2*(4100*(T.vertices+T.darts+1))+2) hm
  simp only [tableCode,dataCode,tableData,prodBits,pairBits_length,natBits_length]
  nlinarith
noncomputable def lengthPolynomial : Polynomial ℕ := 10000*(Polynomial.X+1)^2
 theorem codeLength_le_eval (T : GraphTables.Table) :
    (tableCode T).length ≤ lengthPolynomial.eval (T.vertices+T.darts) := by
  simpa only [lengthPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using codeLength_le T
end TableMachine
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
