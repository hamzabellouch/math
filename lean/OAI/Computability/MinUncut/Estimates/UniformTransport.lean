import Mathlib
import OAI.Computability.MinUncut.Encoding.UniformEncoding

namespace OAI

namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P Q : Type} [Primcodable P] [Primcodable Q] {A B C Γ : P → Type}

def ofEquiv (a : UEncoding P A) (e : ∀p,B p ≃ A p) : UEncoding P B where
  enc p := ⟨(a.enc p).size,(e p).trans (a.enc p).code⟩
  computableSize := a.computableSize
lemma map_to (a : UEncoding P A) (e : ∀p,B p ≃ A p) :
    (a.ofEquiv e).Map a (fun p x=>e p x) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma map_from (a : UEncoding P A) (e : ∀p,B p ≃ A p) :
    a.Map (a.ofEquiv e) (fun p x=>(e p).symm x) :=
  ⟨Prod.snd,Computable.snd,by intro p x; exact congrArg Fin.val ((a.enc p).code.congr_arg ((e p).apply_symm_apply x)).symm⟩

def pullback (a : UEncoding P A) (f : Q → P) (hf : Computable f) : UEncoding Q (fun q=>A (f q)) where
  enc q := a.enc (f q)
  computableSize := a.computableSize.comp hf
lemma Map.pullback {a : UEncoding P A} {b : UEncoding P B} {g : ∀p,A p → B p}
    (hg : a.Map b g) {f : Q → P} (hf : Computable f) :
    (a.pullback f hf).Map (b.pullback f hf) (fun q x=>g (f q) x) := by
  obtain ⟨g',hg',hg⟩:=hg
  refine ⟨fun q=>g' (f q.1,q.2),hg'.comp ((hf.comp Computable.fst).pair Computable.snd),?_⟩
  intro q x
  exact hg (f q) x

lemma Map.first {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} (hf : a.Map b f) :
    (a.prod c).Map b (fun p x=>f p x.1) := map_comp (map_fst a c) hf
lemma Map.second {a : UEncoding P A} {b : UEncoding P B} {c : UEncoding P C}
    {f : ∀p,A p → B p} (hf : a.Map b f) :
    (c.prod a).Map b (fun p x=>f p x.2) := map_comp (map_snd c a) hf

lemma Map.specialize {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,Γ p × A p → B p} (hf : (g.prod a).Map b f)
    {x : ∀p,Γ p → A p} (hx : g.Map a x) :
    g.Map b (fun p s=>f p (s,x p s)) := map_comp (map_pair (map_id g) hx) hf

end UEncoding

namespace UEncoding
variable {P : Type} [Primcodable P] {A B C Γ : P → Type}
variable {p : P}
def sum (a : UEncoding P A) (b : UEncoding P B) : UEncoding P (fun p=>A p ⊕ B p) where
  enc p := (a.enc p).sum (b.enc p)
  computableSize := ca_add a.computableSize b.computableSize
omit [Primcodable P] in
lemma sum_code_inl (a : Encoding (A p)) (b : Encoding (B p)) (x : A p) :
    ((a.sum b).code (Sum.inl x)).val=(a.code x).val := rfl
omit [Primcodable P] in
lemma sum_code_inr (a : Encoding (A p)) (b : Encoding (B p)) (x : B p) :
    ((a.sum b).code (Sum.inr x)).val=a.size+(b.code x).val := rfl
lemma map_inl (a : UEncoding P A) (b : UEncoding P B) :
    a.Map (a.sum b) (fun _ x=>Sum.inl x) :=
  ⟨Prod.snd, Computable.snd, by intro p x; rfl⟩
lemma map_inr (a : UEncoding P A) (b : UEncoding P B) :
    b.Map (a.sum b) (fun _ x=>Sum.inr x) :=
  ⟨fun q=>(a.enc q.1).size+q.2,
    ca_add (a.computableSize.comp Computable.fst) Computable.snd,
    by intro p x; rfl⟩
lemma map_case {g : UEncoding P Γ} {a : UEncoding P A} {b : UEncoding P B}
    {c : UEncoding P C} {f : ∀p,Γ p × A p → C p} {h : ∀p,Γ p × B p → C p}
    (hf : (g.prod a).Map c f) (hh : (g.prod b).Map c h) :
    (g.prod (a.sum b)).Map c (fun p x=>Sum.elim (fun y=>f p (x.1,y)) (fun y=>h p (x.1,y)) x.2) := by
  obtain ⟨f',hf',hf⟩:=hf
  obtain ⟨h',hh',hh⟩:=hh
  let leftSize : P × ℕ → ℕ := fun q=>(a.enc q.1).size
  let rightSize : P × ℕ → ℕ := fun q=>(b.enc q.1).size
  let tag : P × ℕ → ℕ := fun q=>q.2 % (leftSize q+rightSize q)
  let ctxt : P × ℕ → ℕ := fun q=>q.2 / (leftSize q+rightSize q)
  have hl : Computable leftSize := a.computableSize.comp Computable.fst
  have hr : Computable rightSize := b.computableSize.comp Computable.fst
  have ht : Computable tag := ca_mod Computable.snd (ca_add hl hr)
  have hc : Computable ctxt := ca_div Computable.snd (ca_add hl hr)
  let raw : P × ℕ → ℕ := fun q=>if tag q<leftSize q then f' (q.1,ctxt q*leftSize q+tag q)
    else h' (q.1,ctxt q*rightSize q+(tag q-leftSize q))
  have hraw : Computable raw :=
    (Computable.cond (ca_natLt ht hl).decide (hf'.comp (Computable.fst.pair (ca_add (ca_mul hc hl) ht)))
      (hh'.comp (Computable.fst.pair (ca_add (ca_mul hc hr) (ca_sub ht hl))))).of_eq (by intro q; simp only [raw,Bool.cond_eq_ite,decide_eq_true_eq])
  refine ⟨raw,hraw,?_⟩
  intro p ⟨s,z⟩
  have hz : (((a.enc p).sum (b.enc p)).code z).val<(a.enc p).size+(b.enc p).size :=
    (((a.enc p).sum (b.enc p)).code z).isLt
  have hs : 0<(a.enc p).size+(b.enc p).size := by exact Nat.zero_lt_of_lt hz
  have hc' : ctxt (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=((g.enc p).code s).val := by
    simp only [ctxt,leftSize,rightSize]
    change ((((a.enc p).sum (b.enc p)).code z).val+((a.enc p).size+(b.enc p).size)*((g.enc p).code s).val)/
      ((a.enc p).size+(b.enc p).size)=_
    rw [Nat.add_mul_div_left _ _ hs,Nat.div_eq_of_lt hz,Nat.zero_add]
  have ht' : tag (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=(((a.enc p).sum (b.enc p)).code z).val := by
    simp only [tag,leftSize,rightSize]
    change ((((a.enc p).sum (b.enc p)).code z).val+((a.enc p).size+(b.enc p).size)*((g.enc p).code s).val)%
      ((a.enc p).size+(b.enc p).size)=_
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hz]
  change raw (p,(((g.enc p).prod ((a.enc p).sum (b.enc p))).code (s,z)).val)=_
  dsimp only [raw]
  rw [hc',ht']
  cases z with
  | inl x =>
    have he:=hf p (s,x)
    change f' (p,(((g.enc p).prod (a.enc p)).code (s,x)).val)=_ at he
    rw [prod_code] at he
    simpa only [show (((a.enc p).sum (b.enc p)).code (.inl x)).val=((a.enc p).code x).val from rfl,
      leftSize,rightSize,((a.enc p).code x).isLt,ite_true,Sum.elim_inl] using he
  | inr x =>
    have he:=hh p (s,x)
    change h' (p,(((g.enc p).prod (b.enc p)).code (s,x)).val)=_ at he
    rw [prod_code] at he
    simpa only [show (((a.enc p).sum (b.enc p)).code (.inr x)).val=(a.enc p).size+((b.enc p).code x).val from rfl,
      leftSize,rightSize,Nat.add_sub_cancel_left,Nat.not_lt.mpr (Nat.le_add_right _ _),ite_false,Sum.elim_inr] using he
end UEncoding
end MinUncut.Preprocess

end OAI
