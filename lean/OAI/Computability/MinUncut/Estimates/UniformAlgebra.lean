import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformTransport
import OAI.Computability.MinUncut.Estimates.UniformRestrict
import OAI.Computability.MinUncut.Encoding.QuestionEncoding

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [AddCommMonoid X]

lemma c_rangeSum {f : P → ℕ → X} (hf : Computable₂ f)
    (hadd : Computable₂ (fun x y : X=>x+y)) :
    Computable₂ (fun p n=>((List.range n).map (f p)).sum) := by
  have hh := Computable.nat_rec (α:=P × ℕ) (σ:=X) Computable.snd
    (Computable.const 0)
    (hadd.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,
        List.sum_singleton,ih])

namespace UEncoding
variable {A B Γ : P → Type}
omit [AddCommMonoid X] in
lemma Out.toFixed {a : UEncoding P A} {b : Encoding X} [Finite X]
    {f : ∀p,A p → X} (hf : a.Out f) : a.Map (fixed b) f := by
  obtain ⟨f',hr,he⟩:=hf
  exact ⟨_,(Primrec.dom_finite (fun x=>(b.code x).val)).to_comp.comp hr,
    by intro p x; dsimp only; rw [he]; rfl⟩

lemma out_sum {g : UEncoding P Γ} {a : UEncoding P A}
    [∀p,Fintype (A p)] {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f)
    (hadd : Computable₂ (fun x y : X=>x+y)) :
    g.Out (fun p s=>∑x,f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).sum,
    (c_rangeSum hr hadd).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  have he : ((a.enc p).enumerate.map (fun x=>f p (s,x))).sum=∑x,f p (s,x) := by
    classical
    have ht : (a.enc p).enumerate.toFinset=Finset.univ := by ext x; simp [(a.enc p).mem_enumerate x]
    rw [← List.sum_toFinset _ (a.enc p).nodup_enumerate,ht]
  rw [←he,Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

instance primcodableF₂ : Primcodable MinUncut.Inner.F₂ :=
  Primcodable.ofEquiv (Fin 2) MinUncut.Outer.fieldEncoding.code

abbrev field (P : Type) [Primcodable P] := fixed (P:=P) MinUncut.Outer.fieldEncoding

lemma out_field (a : UEncoding P A) {f : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) : a.Out f := hf.out 0
lemma map_field_add {a : UEncoding P A} {f g : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) (hg : a.Map (field P) g) :
    a.Map (field P) (fun p x=>f p x+g p x) :=
  ((out_field a hf).map₂ (out_field a hg) (Primrec.dom_finite _).to_comp).toFixed
lemma map_field_mul {a : UEncoding P A} {f g : ∀p,A p → MinUncut.Inner.F₂}
    (hf : a.Map (field P) f) (hg : a.Map (field P) g) :
    a.Map (field P) (fun p x=>f p x*g p x) :=
  ((out_field a hf).map₂ (out_field a hg) (Primrec.dom_finite _).to_comp).toFixed
lemma map_field_sum {g : UEncoding P Γ} {a : UEncoding P A} [∀p,Fintype (A p)]
    {f : ∀p,Γ p × A p → MinUncut.Inner.F₂} (hf : (g.prod a).Map (field P) f) :
    g.Map (field P) (fun p s=>∑x,f p (s,x)) :=
  (out_sum (out_field _ hf) (Primrec.dom_finite _).to_comp).toFixed
end UEncoding
end MinUncut.Preprocess

end

end OAI
