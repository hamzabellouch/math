import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformRestrict

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open scoped BigOperators
variable {P X : Type} [Primcodable P] [Primcodable X] [CommMonoid X]
lemma c_rangeProd {f : P → ℕ → X} (hf : Computable₂ f)
    (hmul : Computable₂ (fun x y : X=>x*y)) :
    Computable₂ (fun p n=>((List.range n).map (f p)).prod) := by
  have hh := Computable.nat_rec (α:=P × ℕ) (σ:=X) Computable.snd
    (Computable.const 1)
    (hmul.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  exact hh.of_eq (by
    intro p
    induction p.2 with
    | zero => rfl
    | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,List.prod_append,
        List.prod_singleton,ih])

namespace UEncoding
variable {A B Γ : P → Type}
lemma out_prod {g : UEncoding P Γ} {a : UEncoding P A}
    [∀p,Fintype (A p)] {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f)
    (hmul : Computable₂ (fun x y : X=>x*y)) :
    g.Out (fun p s=>∏x,f p (s,x)) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).prod,
    (c_rangeProd hr hmul).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  have he : ((a.enc p).enumerate.map (fun x=>f p (s,x))).prod=∏x,f p (s,x) := by
    classical
    have ht : (a.enc p).enumerate.toFinset=Finset.univ := by ext x; simp [(a.enc p).mem_enumerate x]
    rw [← List.prod_toFinset _ (a.enc p).nodup_enumerate,ht]
  rw [←he,Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

omit [Primcodable X] [CommMonoid X] in
lemma computableCard (a : UEncoding P A) [∀p,Fintype (A p)] : Computable (fun p=>Fintype.card (A p)) :=
  a.computableSize.of_eq (fun p=>(Fintype.card_congr (a.enc p).code).trans (Fintype.card_fin _)|>.symm)

end UEncoding
end MinUncut.Preprocess

end

end OAI
