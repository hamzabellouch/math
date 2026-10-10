import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformRestrict
import OAI.Computability.MinUncut.Estimates.UniformTransport

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A : P → Type}
  {X : Type} [Primcodable X]
lemma Out.pullback {a : UEncoding P A} {g : ∀p,A p → X}
    (hg : a.Out g) {f : Q → P} (hf : Computable f) :
    (a.pullback f hf).Out (fun q x=>g (f q) x) := by
  obtain ⟨g',hgr,hg⟩:=hg
  exact ⟨fun q=>g' (f q.1,q.2),hgr.comp ((hf.comp Computable.fst).pair Computable.snd),
    by intro q x; exact hg (f q) x⟩
lemma Out.cons {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → List X}
    (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>f p x::g p x) :=
  hf.map₂ hg Primrec.list_cons.to_comp
lemma out_boolNat {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Map bool f) :
    a.Out (fun p x=>(f p x).toNat) :=
  (hf.out false).map (Primrec.dom_bool Bool.toNat).to_comp
end MinUncut.Preprocess.UEncoding

end

end OAI
