import Mathlib
import OAI.Computability.MinUncut.Encoding.UniformEncoding

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}

def fixed {X : Type} (e : Encoding X) : UEncoding P (fun _=>X) :=
  ⟨fun _=>e,Computable.const e.size⟩
def bool : UEncoding P (fun _=>Bool) := fixed Encoding.bool
def fin (n : P → ℕ) (hn : Computable n) : UEncoding P (fun p=>Fin (n p)) :=
  ⟨fun p=>Encoding.fin (n p),hn⟩

lemma map_const {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,B p}
    (hf : Computable (fun p=>((b.enc p).code (f p)).val)) :
    a.Map b (fun p _=>f p) :=
  ⟨_,hf.comp Computable.fst,by intros; rfl⟩

lemma bool_code (x : Bool) : (Encoding.bool.code x).val=x.toNat := by
  cases x <;> rfl

lemma map_bool_eq {a : UEncoding P A} {b : UEncoding P B}
    {f g : ∀p,A p → B p} [∀p,DecidableEq (B p)]
    (hf : a.Map b f) (hg : a.Map b g) :
    a.Map bool (fun p x=>decide (f p x=g p x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>(decide (f' q=g' q)).toNat,?_,?_⟩
  · exact (Primrec.dom_bool Bool.toNat).to_comp.comp
      (Primrec.eq.decide.to_comp.comp hf' hg')
  · intro p x
    dsimp only
    rw [hf,hg]
    change _=(Encoding.bool.code _).val
    rw [bool_code]
    congr 2
    exact propext (Fin.val_inj.trans (b.enc p).code.injective.eq_iff)

lemma map_cond {a : UEncoding P A} {b : UEncoding P B}
    {c : ∀p,A p → Bool} {f g : ∀p,A p → B p}
    (hc : a.Map bool c) (hf : a.Map b f) (hg : a.Map b g) :
    a.Map b (fun p x=>if c p x then f p x else g p x) := by
  obtain ⟨c',hc',hc⟩:=hc
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>if c' q=1 then f' q else g' q,?_,?_⟩
  · exact (Computable.cond (Primrec.eq.decide.to_comp.comp hc' (Computable.const 1)) hf' hg').of_eq (by intro q; simp)
  · intro p x
    dsimp only
    rw [hc,hf,hg]
    change (if (Encoding.bool.code (c p x)).val=1 then _ else _)=_
    rw [bool_code]
    cases h:c p x <;> simp

lemma map_fixed {X Y : Type} (a : Encoding X) (b : Encoding Y) (f : X → Y) :
    (fixed (P:=P) a).Map (fixed b) (fun _ x=>f x) := by
  let table := List.ofFn (fun i : Fin a.size=>(b.code (f (a.code.symm i))).val)
  refine ⟨fun q=>(table[q.2]?).getD 0,?_,?_⟩
  · exact Primrec.option_getD_default.to_comp.comp
      ((Primrec.list_getElem?₁ table).to_comp.comp Computable.snd)
  · intro p x
    dsimp only
    change (table[(a.code x).val]?).getD 0=(b.code (f x)).val
    simp [table,(a.code x).isLt]

lemma map_fixed_apply {X Y : Type} {a : UEncoding P A} (b : Encoding X) (c : Encoding Y)
    (op : X → Y) {f : ∀p,A p → X} (hf : a.Map (fixed b) f) :
    a.Map (fixed c) (fun p x=>op (f p x)) :=
  map_comp hf (map_fixed b c op)

lemma map_binary {X Y Z : Type} {a : UEncoding P A}
    (b : Encoding X) (c : Encoding Y) (d : Encoding Z) (op : X → Y → Z)
    {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Map (fixed b) f) (hg : a.Map (fixed c) g) :
    a.Map (fixed d) (fun p x=>op (f p x) (g p x)) :=
  map_comp (map_pair hf hg) (map_fixed (b.prod c) d (fun x=>op x.1 x.2))

lemma map_not {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Map bool f) :
    a.Map bool (fun p x=>!(f p x)) :=
  map_fixed_apply Encoding.bool Encoding.bool Bool.not hf
lemma map_and {a : UEncoding P A} {f g : ∀p,A p → Bool}
    (hf : a.Map bool f) (hg : a.Map bool g) : a.Map bool (fun p x=>f p x && g p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.and hf hg
lemma map_or {a : UEncoding P A} {f g : ∀p,A p → Bool}
    (hf : a.Map bool f) (hg : a.Map bool g) : a.Map bool (fun p x=>f p x || g p x) :=
  map_binary Encoding.bool Encoding.bool Encoding.bool Bool.or hf hg

end UEncoding
end MinUncut.Preprocess

end

end OAI
