import Mathlib

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.LiteralVector
open Turing Turing.ToPartrec

/-- A partial tuple-valued program compiles on every successful input. -/
theorem partial_code_exists {n m : ℕ} (f : List.Vector ℕ n→.List.Vector ℕ m) (hf : Partrec f) :
    ∃c : Code,∀v w,w∈f v→w.val∈Code.eval c v.val := by
  induction m with
  | zero=>
    refine ⟨.nil,?_⟩
    intro v w hw
    have h : w.val=[] := List.eq_nil_of_length_eq_zero w.property
    simp [h]
  | succ m ih=>
    have hh : Partrec (fun v=>(f v).map List.Vector.head) :=
      hf.map (Primrec.vector_head.comp Primrec.snd).to_comp.to₂
    obtain ⟨a,ha⟩:=Code.exists_code (Nat.Partrec'.part_iff.mpr hh)
    have ht : Partrec (fun v=>(f v).map List.Vector.tail) :=
      hf.map (Primrec.vector_tail.comp Primrec.snd).to_comp.to₂
    obtain ⟨b,hb⟩:=ih (fun v=>(f v).map List.Vector.tail) ht
    refine ⟨.cons a b,?_⟩
    intro v w hw
    have h₁ : [w.head]∈Code.eval a v.val := by
      rw [ha]
      exact (Part.mem_map_iff _).mpr ⟨w.head,(Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩,rfl⟩
    have h₂ : w.tail.val∈Code.eval b v.val := hb v w.tail ((Part.mem_map_iff _).mpr ⟨w,hw,rfl⟩)
    rw [Code.cons_eval]
    apply Part.mem_bind_iff.mpr
    refine ⟨[w.head],h₁,?_⟩
    apply Part.mem_bind_iff.mpr
    refine ⟨w.tail.val,h₂,?_⟩
    change w.val∈Part.some (w.head::w.tail.val)
    apply Part.mem_some_iff.mpr
    exact (congrArg Subtype.val (List.Vector.cons_head_tail w)).symm

end UniformKServer.LiteralVector

end


end

end OAI
