import Mathlib
import OAI.Combinatorics.UniformKServer.RawProgram

namespace OAI

noncomputable section
                                    
section

namespace UniformKServer.LiteralVector
open Turing Turing.ToPartrec

/-- Compile a tuple-valued total primitive recursive map without changing its
binary list interface by an additional unbounded encoding oracle. -/
theorem code_exists {n m : ℕ} (f : List.Vector ℕ n→List.Vector ℕ m) (hf : Primrec f) :
    ∃c : Code,∀v,Code.eval c v.val=Part.some (f v).val := by
  induction m with
  | zero=>
    refine ⟨.nil,?_⟩
    intro v
    have h : (f v).val=[] := List.eq_nil_of_length_eq_zero (f v).property
    simp [h]
  | succ m ih=>
    have hh : Partrec (fun v=>(Part.some ((f v).head))) :=
      (Primrec.vector_head.comp hf).to_comp
    obtain ⟨a,ha⟩:=Code.exists_code (Nat.Partrec'.part_iff.mpr hh)
    obtain ⟨b,hb⟩:=ih (fun v=>(f v).tail) (Primrec.vector_tail.comp hf)
    refine ⟨.cons a b,?_⟩
    intro v
    simp only [Code.cons_eval,ha,hb,Part.map_eq_map,Part.map_some,Part.bind_eq_bind,Part.bind_some,Part.pure_eq_some]
    congr 1
    exact congrArg Subtype.val (List.Vector.cons_head_tail (f v))

noncomputable def activeCode : Code := Classical.choose (code_exists RawProgram.run RawProgram.primitive_run)
 theorem active_eval (v : List.Vector ℕ 3) :
    Code.eval activeCode v.val=Part.some (RawProgram.run v).val :=
  Classical.choose_spec (code_exists RawProgram.run RawProgram.primitive_run) v

end UniformKServer.LiteralVector

end


end

end OAI
