import Mathlib
import OAI.Computability.MinUncut.Search.RawRationalArithmetic
import OAI.Computability.MinUncut.PCP.Occurrences

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators

structure UEncoding (P : Type) [Primcodable P] (A : P → Type) where
  enc : ∀p, Encoding (A p)
  computableSize : Computable (fun p=>(enc p).size)

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}

def prod (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p × B p) where
  enc p := (a.enc p).prod (b.enc p)
  computableSize := ca_mul a.computableSize b.computableSize

def function (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p → B p) where
  enc p := (a.enc p).function (b.enc p)
  computableSize := ca_pow b.computableSize a.computableSize

def Map (a : UEncoding P A) (b : UEncoding P B) (f : ∀p,A p → B p) : Prop :=
  ∃g : P × ℕ → ℕ, Computable g ∧ ∀p x,g (p,((a.enc p).code x).val)=((b.enc p).code (f p x)).val

lemma map_id (a : UEncoding P A) : a.Map a (fun _ x=>x) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩

lemma map_comp {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} {g : ∀p,B p → C p} (hf : a.Map b f) (hg : b.Map c g) :
    a.Map c (fun p x=>g p (f p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  exact ⟨fun q=>g' (q.1,f' q),hg'.comp (Computable.fst.pair hf'),by intro p x; dsimp only; rw [hf,hg]⟩

lemma prod_code {Left Right : Type} (a : Encoding Left) (b : Encoding Right)
    (x : Left) (y : Right) :
    ((a.prod b).code (x,y)).val=(a.code x).val*b.size+(b.code y).val := by
  change (b.code y).val+b.size*(a.code x).val=_
  ac_rfl

lemma map_pair {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} {g : ∀p,A p → C p} (hf : a.Map b f) (hg : a.Map c g) :
    a.Map (b.prod c) (fun p x=>(f p x,g p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>f' q*(c.enc q.1).size+g' q,?_,?_⟩
  · exact ca_add (ca_mul hf' (c.computableSize.comp Computable.fst)) hg'
  · intro p x
    dsimp only
    rw [hf,hg]
    exact (prod_code _ _ _ _).symm

lemma map_fst (a : UEncoding P A) (b : UEncoding P B) :
    (a.prod b).Map a (fun _ x=>x.1) := by
  refine ⟨fun q=>q.2/(b.enc q.1).size,ca_div Computable.snd (b.computableSize.comp Computable.fst),?_⟩
  intro p ⟨x,y⟩
  change (((b.enc p).code y).val+(b.enc p).size*((a.enc p).code x).val)/(b.enc p).size=_
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt ((b.enc p).code y).isLt),
    Nat.div_eq_of_lt ((b.enc p).code y).isLt,Nat.zero_add]

lemma map_snd (a : UEncoding P A) (b : UEncoding P B) :
    (a.prod b).Map b (fun _ x=>x.2) := by
  refine ⟨fun q=>q.2%(b.enc q.1).size,ca_mod Computable.snd (b.computableSize.comp Computable.fst),?_⟩
  intro p ⟨x,y⟩
  change (((b.enc p).code y).val+(b.enc p).size*((a.enc p).code x).val)%(b.enc p).size=_
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ((b.enc p).code y).isLt]

lemma function_digit {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) (x : X) :
    (((a.function b).code f).val/(b.size^(a.code x).val))%b.size=(b.code (f x)).val := by
  have hh:=congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply
    (fun i=>b.code (f (a.code.symm i)))) (a.code x))
  change (((a.function b).code f).val/(b.size^(a.code x).val))%b.size=
    (b.code (f (a.code.symm (a.code x)))).val at hh
  simpa only [Equiv.symm_apply_apply] using hh

lemma map_apply {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p → A p → B p} {x : ∀p,Γ p → A p}
    (hf : g.Map (a.function b) f) (hx : g.Map a x) :
    g.Map b (fun p s=>f p s (x p s)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨x',hx',hx⟩:=hx
  refine ⟨fun q=>(f' q/(b.enc q.1).size^(x' q))%(b.enc q.1).size,?_,?_⟩
  · exact ca_mod (ca_div hf' (ca_pow (b.computableSize.comp Computable.fst) hx'))
      (b.computableSize.comp Computable.fst)
  · intro p s
    dsimp only
    rw [hf,hx]
    exact function_digit _ _ _ _

lemma function_number {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) :
    ((a.function b).code f).val=
      ∑i : Fin a.size,(b.code (f (a.code.symm i))).val*b.size^i.val := rfl

lemma finRange_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

lemma map_lambda {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p × A p → B p} (hf : (g.prod a).Map b f) :
    g.Map (a.function b) (fun p s x=>f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → ℕ := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)*(b.enc q.1).size^i
  have hr : Computable₂ raw := by
    unfold raw
    exact ca_mul (hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd)))
      (ca_pow (b.computableSize.comp (Computable.fst.comp Computable.fst)) Computable.snd)
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).sum,
    c_boundedSum hr (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  rw [function, function_number,←List.sum_ofFn,List.ofFn_eq_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hh : f' (p, (((g.enc p).prod (a.enc p)).code (s, (a.enc p).code.symm i)).val) =
      ((b.enc p).code (f p (s, (a.enc p).code.symm i))).val :=
    hf p (s, (a.enc p).code.symm i)
  rw [prod_code,Equiv.apply_symm_apply] at hh
  dsimp only [Function.comp_def,raw]
  rw [hh]

end UEncoding
end MinUncut.Preprocess

end

end OAI
