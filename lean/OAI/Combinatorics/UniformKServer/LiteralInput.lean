import Mathlib
import OAI.Combinatorics.UniformKServer.RawBits
import OAI.Combinatorics.UniformKServer.StackPrimitive

namespace OAI

noncomputable section

namespace UniformKServer.LiteralInput
open Turing Turing.PartrecToTM2 Primrec StackCompiler
open scoped Classical

 theorem primitive_trNat : Primrec (fun a : ℕ=>(trNat a).map (FlatTM2.letters (Γ:=Γ'))) := by
  have h : Primrec (fun a : ℕ=>a.bits.map (fun b=>FlatTM2.letters (RawBits.letter b))) :=
    Primrec.list_map RawBits.primitive_bits ((Primrec.dom_finite (fun b : Bool=>FlatTM2.letters (RawBits.letter b))).comp Primrec.snd).to₂
  exact h.of_eq (by intro a;rw [RawBits.trNat_bits,List.map_map];rfl)

 theorem primitive_trList : Primrec (fun xs : List ℕ=>(trList xs).map (FlatTM2.letters (Γ:=Γ'))) := by
  have h : Primrec (fun xs : List ℕ=>xs.foldr (fun a s=>
      (trNat a).map FlatTM2.letters++FlatTM2.letters Γ'.cons::s) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.list_append.comp (primitive_trNat.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp (Primrec.const (FlatTM2.letters Γ'.cons)) (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq (by
    intro xs
    induction xs with
    | nil=>rfl
    | cons a xs ih=>simp only [List.foldr_cons,trList,List.map_append,List.map_cons,ih])

 theorem input_config (c : Turing.ToPartrec.Code) (v : List ℕ) :
    StackPrimitive.ofState (LiteralPartrec.input c v)=
      ((LiteralPartrec.processor c).start,
        (fun i : Fin (Fintype.card K')=>if i=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []),false) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      change ((K'.elim (trList v) [] [] []) (FlatTM2.keys.symm i)).map FlatTM2.letters=_
      have he : (i=FlatTM2.keys K'.main) ↔ FlatTM2.keys.symm i=K'.main := by
        constructor
        · rintro rfl;exact Equiv.symm_apply_apply _ _
        · intro h;exact (Equiv.apply_symm_apply _ i).symm.trans (congrArg FlatTM2.keys h)
      dsimp only
      simp only [he]
      cases FlatTM2.keys.symm i <;> simp [K'.elim]
    · rfl

 theorem primitive_input (c : Turing.ToPartrec.Code) :
    Primrec (fun v=>StackPrimitive.ofState (LiteralPartrec.input c v)) := by
  have h : Primrec (fun v : List ℕ=>
      (((LiteralPartrec.processor c).start,
        (fun i : Fin (Fintype.card K')=>if i=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []),false) :
        StackPrimitive.Config _ (Fintype.card K') (Fintype.card Γ'))) := by
    apply Primrec.pair (Primrec.const _)
    apply Primrec.pair _ (Primrec.const false)
    apply Primrec.fin_curry.mpr
    apply Primrec.ite
    · exact (Primrec.eq.comp Primrec.snd (Primrec.const (FlatTM2.keys K'.main)))
    · exact primitive_trList.comp Primrec.fst
    · exact Primrec.const []
  exact h.of_eq (fun v=>(input_config c v).symm)

end UniformKServer.LiteralInput

end

end OAI
