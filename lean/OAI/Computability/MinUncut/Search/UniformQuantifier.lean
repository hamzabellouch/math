import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformBoolean

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

lemma Map.ofEq {a : UEncoding P A} {b : UEncoding P B}
    {f g : ∀p,A p → B p} (hf : a.Map b f) (h : ∀p x,f p x=g p x) : a.Map b g := by
  obtain ⟨f',hr,hf⟩:=hf
  exact ⟨f',hr,by intro p x; rw [hf,h]⟩

lemma map_true (a : UEncoding P A) : a.Map bool (fun _ _=>true) :=
  map_const (Computable.const 1)
lemma map_false (a : UEncoding P A) : a.Map bool (fun _ _=>false) :=
  map_const (Computable.const 0)

lemma map_forall {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → Bool} [∀p s,Decidable (∀x,f p (s,x)=true)]
    (hf : (g.prod a).Map bool f) :
    g.Map bool (fun p s=>decide (∀x,f p (s,x)=true)) := by
  classical
  have hh := map_bool_eq (map_lambda hf) (map_lambda (map_true (g.prod a)))
  apply hh.ofEq
  intro p s
  apply decide_eq_decide.mpr
  exact ⟨fun h x=>congrFun h x,fun h=>funext h⟩

lemma map_exists {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → Bool} [∀p s,Decidable (∃x,f p (s,x)=true)]
    (hf : (g.prod a).Map bool f) :
    g.Map bool (fun p s=>decide (∃x,f p (s,x)=true)) := by
  classical
  have hh := map_not (map_forall (map_not hf))
  apply hh.ofEq
  intro p s
  rw [←decide_not]
  apply decide_eq_decide.mpr
  simp

def Value (a : UEncoding P A) (f : ∀p,A p → ℕ) : Prop :=
  ∃g : P × ℕ → ℕ, Computable g ∧ ∀p x,g (p,((a.enc p).code x).val)=f p x

lemma value_code (a : UEncoding P A) : a.Value (fun p x=>((a.enc p).code x).val) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma value_const (a : UEncoding P A) {f : P → ℕ} (hf : Computable f) :
    a.Value (fun p _=>f p) := ⟨_,hf.comp Computable.fst,by intros; rfl⟩
lemma Value.comp {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,A p → B p} {g : ∀p,B p → ℕ} (hg : b.Value g) (hf : a.Map b f) :
    a.Value (fun p x=>g p (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨fun q=>g' (q.1,f' q),hrg.comp (Computable.fst.pair hrf),
    by intro p x; dsimp only; rw [hf,hg]⟩
lemma Value.map {a : UEncoding P A} {f : ∀p,A p → ℕ} (hf : a.Value f)
    {g : ℕ → ℕ} (hg : Computable g) : a.Value (fun p x=>g (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  exact ⟨_,hg.comp hrf,by intro p x; dsimp only; rw [hf]⟩
lemma Value.map₂ {a : UEncoding P A} {f g : ∀p,A p → ℕ}
    (hf : a.Value f) (hg : a.Value g) {op : ℕ → ℕ → ℕ} (hop : Computable₂ op) :
    a.Value (fun p x=>op (f p x) (g p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨_,hop.comp hrf hrg,by intro p x; dsimp only; rw [hf,hg]⟩

lemma value_sum {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → ℕ} (hf : (g.prod a).Value f) :
    g.Value (fun p s=>((a.enc p).enumerate.map (fun x=>f p (s,x))).sum) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → ℕ := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>((List.range (a.enc q.1).size).map (raw q)).sum,
    c_boundedSum hr (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  rw [Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hh : f' (p, (((g.enc p).prod (a.enc p)).code (s, (a.enc p).code.symm i)).val) =
      f p (s, (a.enc p).code.symm i) :=
    hf p (s, (a.enc p).code.symm i)
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

end UEncoding
end MinUncut.Preprocess

end

end OAI
