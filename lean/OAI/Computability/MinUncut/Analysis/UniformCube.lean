import Mathlib
import OAI.Computability.MinUncut.Estimates.TemplateExpressions

namespace OAI

section
namespace MinUncut.Preprocess.UEncoding
open MinUncutGames.Foundations.Hastad MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def equationEquiv (X : Type) : Equation X ≃ X × X × X × Bool where
  toFun e := (e.first,e.second,e.third,e.rhs)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def equation (a : UEncoding P A) : UEncoding P (fun p=>Equation (A p)) :=
  (a.prod (a.prod (a.prod bool))).ofEquiv (fun p=>equationEquiv (A p))

lemma map_equation {g : UEncoding P Γ} {a : UEncoding P A}
    {f h j : ∀p,Γ p → A p} {b : ∀p,Γ p → Bool}
    (hf : g.Map a f) (hh : g.Map a h) (hj : g.Map a j) (hb : g.Map bool b) :
    g.Map a.equation (fun p x=>⟨f p x,h p x,j p x,b p x⟩) :=
  map_comp (map_pair hf (map_pair hh (map_pair hj hb)))
    (map_from (a.prod (a.prod (a.prod bool))) (fun p=>equationEquiv (A p)))

lemma map_thirdQuery {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {π : ∀p,Γ p → B p → A p} {f : ∀p,Γ p → A p → Bool}
    {h μ : ∀p,Γ p → B p → Bool}
    (hπ : g.Map (b.function a) π) (hf : g.Map (a.function bool) f)
    (hh : g.Map (b.function bool) h) (hμ : g.Map (b.function bool) μ) :
    g.Map (b.function bool) (fun p x=>thirdQuery (π p x) (f p x) (h p x) (μ p x)) := by
  exact map_lambda (map_xor (map_apply hh.first (map_snd g b))
    (map_xor (map_apply hf.first (map_apply hπ.first (map_snd g b)))
      (map_apply hμ.first (map_snd g b))))

lemma map_padded {g : UEncoding P Γ} {a : UEncoding P A}
    {v f : ∀p,Γ p → A p → Bool} {i : ∀p,Γ p → A p}
    (hv : g.Map (a.function bool) v) (hf : g.Map (a.function bool) f) (hi : g.Map a i) :
    g.Map (a.function bool) (fun p x j=>if v p x j then representative (i p x) (f p x) j else false) :=
  map_lambda (map_cond (map_apply hv.first (map_snd g a))
    (map_apply (map_representative hf hi).first (map_snd g a)) (map_false _))

lemma map_value_zero {g : UEncoding P Γ} {n : P → ℕ} {hn : Computable n}
    {f : ∀p,Γ p → Fin (n p)} (hf : g.Map (fin n hn) f) :
    g.Map bool (fun p x=>decide ((f p x).val=0)) := by
  obtain ⟨f',hf',hf⟩:=hf
  refine ⟨fun q=>(decide (f' q=0)).toNat,
    (Primrec.dom_bool Bool.toNat).to_comp.comp
      (Primrec.eq.decide.to_comp.comp hf' (Computable.const 0)),?_⟩
  intro p x
  dsimp only
  rw [hf]
  change _=(Encoding.bool.code _).val
  rw [bool_code]
  rfl
end MinUncut.Preprocess.UEncoding

end

end OAI
