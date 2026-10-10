import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformBoolean
import OAI.Computability.MinUncut.Estimates.UniformTransport

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def optionEquiv (X : Type) : Option X ≃ X ⊕ Unit where
  toFun x := match x with | some a => .inl a | none => .inr ()
  invFun x := match x with | .inl a => some a | .inr _ => none
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x with | inl a => rfl | inr a => cases a; rfl

def option (a : UEncoding P A) : UEncoding P (fun p=>Option (A p)) :=
  (a.sum (fixed Encoding.unit)).ofEquiv (fun p=>optionEquiv (A p))
lemma option_code_some (a : UEncoding P A) (p : P) (x : A p) :
    ((a.option.enc p).code (some x)).val=((a.enc p).code x).val := rfl
lemma option_code_none (a : UEncoding P A) (p : P) :
    ((a.option.enc p).code none).val=(a.enc p).size := by
  change (a.enc p).size+0=_
  omega

lemma enumeration_codes {X : Type} (a : Encoding X) :
    a.enumerate.map (fun x=>(a.code x).val)=List.range a.size := by
  simp only [Encoding.enumerate,List.map_ofFn]
  rw [List.ofFn_eq_map]
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using finRange_values a.size

lemma map_find (a : UEncoding P A) :
    (a.function bool).Map a.option (fun p f=>(a.enc p).enumerate.find? f) := by
  let search : ℕ × ℕ → ℕ := fun q=>(List.range q.1).findIdx (fun i=>decide ((q.2/2^i)%2=1))
  have hs : Primrec search := by
    exact Primrec.list_findIdx (Primrec.list_range.comp Primrec.fst)
      (Primrec.eq.decide.comp₂
        (Primrec.nat_mod.comp₂
          (Primrec.nat_div.comp₂ (Primrec.snd.comp Primrec.fst).to₂
            (primrec_pow.comp₂ (Primrec.const 2).to₂ Primrec.snd.to₂))
          (Primrec.const 2).to₂) (Primrec.const 1).to₂)
  refine ⟨fun q=>search ((a.enc q.1).size,q.2),hs.to_comp.comp
    ((a.computableSize.comp Computable.fst).pair Computable.snd),?_⟩
  intro p f
  have he : search ((a.enc p).size,((a.function bool).enc p).code f|>.val)=
      (a.enc p).enumerate.findIdx f := by
    unfold search
    rw [←enumeration_codes (a.enc p),List.findIdx_map]
    congr 1
    funext x
    have hd:=function_digit (a.enc p) Encoding.bool f x
    change decide ((((a.enc p).function Encoding.bool).code f|>.val)/Encoding.bool.size^((a.enc p).code x|>.val)%Encoding.bool.size=1)=f x
    rw [hd,bool_code]
    cases f x <;> rfl
  dsimp only
  rw [he,List.find?_eq_getElem?_findIdx]
  by_cases h:(a.enc p).enumerate.findIdx f < (a.enc p).size
  · rw [show (a.enc p).enumerate=((List.ofFn (a.enc p).code.symm)) from rfl]
    dsimp only [Encoding.enumerate] at h
    rw [List.getElem?_ofFn,dite_eq_left h]
    simp only [option_code_some,Equiv.apply_symm_apply]
  · have hn : (a.enc p).enumerate.findIdx f=(a.enc p).size :=
      le_antisymm (by simpa using List.findIdx_le_length (p:=f) (xs:=(a.enc p).enumerate)) (by omega)
    rw [hn,List.getElem?_eq_none (by simp),option_code_none]

lemma map_find_apply {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p → A p → Bool} (hf : g.Map (a.function bool) f) :
    g.Map a.option (fun p x=>(a.enc p).enumerate.find? (f p x)) := map_comp hf (map_find a)

lemma map_option_elim {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p → B p} {h : ∀p,Γ p × A p → B p}
    (hf : g.Map b f) (hh : (g.prod a).Map b h) :
    (g.prod a.option).Map b (fun p x=>x.2.elim (f p x.1) (fun y=>h p (x.1,y))) := by
  have hc:=map_case hh (hf.first (c:=fixed Encoding.unit))
  have ht : (g.prod a.option).Map (g.prod (a.sum (fixed Encoding.unit)))
      (fun p x=>(x.1,optionEquiv (A p) x.2)) :=
    map_pair (map_fst g a.option)
      (map_comp (map_snd g a.option) (map_to (a.sum (fixed Encoding.unit)) (fun p=>optionEquiv (A p))))
  obtain ⟨raw, hraw, hraw_spec⟩ := map_comp ht hc
  refine ⟨raw, hraw, ?_⟩
  rintro parameter ⟨context, value⟩
  cases value <;> exact hraw_spec parameter _

end UEncoding
end MinUncut.Preprocess

end

end OAI
