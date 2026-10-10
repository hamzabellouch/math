import Mathlib
import OAI.Computability.MinUncut.Estimates.UniformBoolean

namespace OAI

namespace MinUncut.Preprocess
open MinUncutGames.Foundations.Hastad.SourceOccurrences
namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}

def goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) : List ℕ :=
  (List.range (a.enc p).size).filter (fun n=>if h:n<(a.enc p).size then b p ((a.enc p).code.symm ⟨n,h⟩) else false)
lemma goodCodes_nodup (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) :
    (goodCodes a b p).Nodup := List.nodup_range.filter _
lemma mem_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) (n : ℕ) :
    n∈goodCodes a b p ↔ ∃h:n<(a.enc p).size,b p ((a.enc p).code.symm ⟨n,h⟩)=true := by
  simp only [goodCodes,List.mem_filter,List.mem_range]
  by_cases hn:n<(a.enc p).size <;> simp [hn]
lemma original_mem_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) (x : A p) :
    ((a.enc p).code x).val∈goodCodes a b p ↔ b p x=true := by
  rw [mem_goodCodes]
  simp only [Equiv.symm_apply_apply,Fin.eta]
  exact ⟨fun h=>h.2,fun h=>⟨((a.enc p).code x).isLt,h⟩⟩

lemma computable_goodCodes (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    Computable (goodCodes a b) := by
  obtain ⟨f,hf,h⟩:=hb
  have hr : Computable₂ (fun p n=>if f (p,n)=1 then [n] else []) := by
    exact (Computable.cond (Primrec.eq.decide.to_comp.comp hf (Computable.const 1))
      (Computable.list_cons.comp Computable.snd (Computable.const []))
      (Computable.const [])).of_eq (by intro q; simp)
  have hh := Primrec.list_flatten.to_comp.comp ((c_rangeMap hr).comp Computable.id a.computableSize)
  apply hh.of_eq
  intro p
  change (List.range (a.enc p).size).flatMap _=_
  rw [show goodCodes a b p=(List.range (a.enc p).size).flatMap
    (fun n=>if (if h:n<(a.enc p).size then b p ((a.enc p).code.symm ⟨n,h⟩) else false) then [n] else []) by
      unfold goodCodes
      generalize List.range (a.enc p).size = xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.filter_cons,List.flatMap_cons,ih]; split_ifs <;> simp_all]
  apply List.flatMap_congr
  intro n hn
  have hn' : n<(a.enc p).size := List.mem_range.mp hn
  have ht := h p ((a.enc p).code.symm ⟨n,hn'⟩)
  simp only [Equiv.apply_symm_apply] at ht
  dsimp only [id]
  simp only [dite_eq_left hn',ht]
  change (if (Encoding.bool.code _).val=1 then _ else _) = _
  rw [bool_code]
  cases b p ((a.enc p).code.symm ⟨n,hn'⟩) <;> rfl

def restrictEquiv (a : UEncoding P A) (b : ∀p,A p → Bool) (p : P) :
    {x:A p // b p x=true} ≃ {n:ℕ // n∈goodCodes a b p} where
  toFun x := ⟨((a.enc p).code x.val).val,(original_mem_goodCodes a b p x).mpr x.property⟩
  invFun n := ⟨(a.enc p).code.symm ⟨n.val,((mem_goodCodes a b p n).mp n.property).choose⟩,
    ((mem_goodCodes a b p n).mp n.property).choose_spec⟩
  left_inv x := by apply Subtype.ext; exact (a.enc p).code.symm_apply_apply x.val
  right_inv n := by apply Subtype.ext; exact congrArg Fin.val ((a.enc p).code.apply_symm_apply _)

def restrict (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    UEncoding P (fun p=>{x:A p // b p x=true}) where
  enc p := ⟨(goodCodes a b p).length,(restrictEquiv a b p).trans
    ((goodCodes_nodup a b p).getEquiv (goodCodes a b p)).symm⟩
  computableSize := Computable.list_length.comp (computable_goodCodes a b hb)

lemma restrict_code (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b)
    (p : P) (x : {x:A p // b p x=true}) :
    (((a.restrict b hb).enc p).code x).val=(goodCodes a b p).idxOf (((a.enc p).code x.val).val) := rfl

lemma map_restrict_val (a : UEncoding P A) (b : ∀p,A p → Bool) (hb : a.Map bool b) :
    (a.restrict b hb).Map a (fun _ x=>x.val) := by
  refine ⟨fun q=>((goodCodes a b q.1)[q.2]?).getD 0,?_,?_⟩
  · exact Primrec.option_getD_default.to_comp.comp
      (Computable.list_getElem?.comp ((computable_goodCodes a b hb).comp Computable.fst) Computable.snd)
  · intro p x
    dsimp only
    rw [restrict_code,List.getElem?_idxOf (by exact (original_mem_goodCodes a b p x).mpr x.property)]
    rfl

lemma map_restrict_mk {g : UEncoding P Γ} {a : UEncoding P A} {b : ∀p,A p → Bool}
    (hb : a.Map bool b) {f : ∀p,Γ p → A p} (hf : g.Map a f)
    (h : ∀p x,b p (f p x)=true) :
    g.Map (a.restrict b hb) (fun p x=>⟨f p x,h p x⟩) := by
  obtain ⟨f',hf',he⟩:=hf
  refine ⟨fun q=>(goodCodes a b q.1).idxOf (f' q),?_,?_⟩
  · exact Primrec.list_idxOf.to_comp.comp hf' ((computable_goodCodes a b hb).comp Computable.fst)
  · intro p x
    dsimp only
    rw [he,restrict_code]

end UEncoding

namespace UEncoding
variable {P : Type} [Primcodable P] {A B Γ : P → Type}
variable {X Y Z : Type} [Primcodable X] [Primcodable Y] [Primcodable Z]

def Out (a : UEncoding P A) (f : ∀p,A p → X) : Prop :=
  ∃g : P × ℕ → X, Computable g ∧ ∀p x,g (p,((a.enc p).code x).val)=f p x
lemma Out.ofEq {a : UEncoding P A} {f g : ∀p,A p → X} (hf : a.Out f)
    (h : ∀p x,f p x=g p x) : a.Out g := by
  obtain ⟨f',hr,hh⟩:=hf
  exact ⟨f',hr,fun p x=>(hh p x).trans (h p x)⟩
lemma out_const (a : UEncoding P A) {f : P → X} (hf : Computable f) :
    a.Out (fun p _=>f p) := ⟨_,hf.comp Computable.fst,by intros; rfl⟩
lemma out_code (a : UEncoding P A) : a.Out (fun p x=>((a.enc p).code x).val) :=
  ⟨Prod.snd,Computable.snd,by intros; rfl⟩
lemma Out.comp {a : UEncoding P A} {b : UEncoding P B}
    {f : ∀p,A p → B p} {g : ∀p,B p → X} (hg : b.Out g) (hf : a.Map b f) :
    a.Out (fun p x=>g p (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨fun q=>g' (q.1,f' q),hrg.comp (Computable.fst.pair hrf),
    by intro p x; dsimp only; rw [hf,hg]⟩
lemma Out.map {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f)
    {g : X → Y} (hg : Computable g) : a.Out (fun p x=>g (f p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  exact ⟨_,hg.comp hrf,by intro p x; dsimp only; rw [hf]⟩
lemma Out.map₂ {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Out f) (hg : a.Out g) {op : X → Y → Z} (hop : Computable₂ op) :
    a.Out (fun p x=>op (f p x) (g p x)) := by
  obtain ⟨f',hrf,hf⟩:=hf
  obtain ⟨g',hrg,hg⟩:=hg
  exact ⟨_,hop.comp hrf hrg,by intro p x; dsimp only; rw [hf,hg]⟩
lemma Out.pair {a : UEncoding P A} {f : ∀p,A p → X} {g : ∀p,A p → Y}
    (hf : a.Out f) (hg : a.Out g) : a.Out (fun p x=>(f p x,g p x)) :=
  hf.map₂ hg (Computable.fst.pair Computable.snd)
lemma Out.first {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X}
    (hf : a.Out f) : (a.prod b).Out (fun p x=>f p x.1) := hf.comp (map_fst a b)
lemma Out.second {a : UEncoding P A} {b : UEncoding P B} {f : ∀p,A p → X}
    (hf : a.Out f) : (b.prod a).Out (fun p x=>f p x.2) := hf.comp (map_snd b a)

lemma out_list {g : UEncoding P Γ} {a : UEncoding P A}
    {f : ∀p,Γ p × A p → X} (hf : (g.prod a).Out f) :
    g.Out (fun p s=>(a.enc p).enumerate.map (fun x=>f p (s,x))) := by
  obtain ⟨f',hf',hf⟩:=hf
  let raw : (P × ℕ) → ℕ → X := fun q i=>f' (q.1,q.2*(a.enc q.1).size+i)
  have hr : Computable₂ raw := by
    unfold raw
    exact hf'.comp ((Computable.fst.comp Computable.fst).pair
      (ca_add (ca_mul (Computable.snd.comp Computable.fst)
        (a.computableSize.comp (Computable.fst.comp Computable.fst))) Computable.snd))
  refine ⟨fun q=>(List.range (a.enc q.1).size).map (raw q),
    (c_rangeMap hr).comp Computable.id (a.computableSize.comp Computable.fst),?_⟩
  intro p s
  dsimp only
  rw [Encoding.enumerate,List.ofFn_eq_map,List.map_map]
  rw [←finRange_values ((a.enc p).size),List.map_map]
  apply List.map_congr_left
  intro i hi
  have hh:=hf p (s,(a.enc p).code.symm i)
  change f' (p,(((g.enc p).prod (a.enc p)).code (s,(a.enc p).code.symm i)).val)=_ at hh
  rw [prod_code,Equiv.apply_symm_apply] at hh
  exact hh

lemma Out.enumerate {a : UEncoding P A} {f : ∀p,A p → X} (hf : a.Out f) :
    Computable (fun p=>(a.enc p).enumerate.map (f p)) := by
  have hh:=out_list (g:=fixed Encoding.unit) hf.second
  obtain ⟨h,hr,he⟩:=hh
  exact (hr.comp (Computable.id.pair (Computable.const 0))).of_eq (fun p=>he p ())

lemma fixed_out (a : Encoding X) (x₀ : X) : (fixed (P:=P) a).Out (fun _ x=>x) := by
  let table:=a.enumerate
  refine ⟨fun q=>(table[q.2]?).getD x₀,?_,?_⟩
  · exact Primrec.option_getD.to_comp.comp
      ((Primrec.list_getElem?₁ table).to_comp.comp Computable.snd) (Computable.const x₀)
  · intro p x
    dsimp only
    change (a.enumerate[(a.code x).val]?).getD x₀=x
    simp [Encoding.enumerate,(a.code x).isLt]
lemma Map.out {a : UEncoding P A} {b : Encoding X} {f : ∀p,A p → X}
    (hf : a.Map (fixed b) f) (x₀ : X) : a.Out f := (fixed_out b x₀).comp hf
lemma Out.toBool {a : UEncoding P A} {f : ∀p,A p → Bool} (hf : a.Out f) : a.Map bool f := by
  obtain ⟨f',hr,h⟩:=hf
  refine ⟨fun q=>(f' q).toNat,(Primrec.dom_bool Bool.toNat).to_comp.comp hr,?_⟩
  intro p x
  dsimp only
  rw [h]
  exact (bool_code _).symm
lemma Out.toFin {a : UEncoding P A} {n : P → ℕ} (hn : Computable n)
    {f : ∀p,A p → Fin (n p)} (hf : a.Out (fun p x=>(f p x).val)) :
    a.Map (fin n hn) f := hf
lemma Out.cond {a : UEncoding P A} {c : ∀p,A p → Bool} {f g : ∀p,A p → X}
    (hc : a.Map bool c) (hf : a.Out f) (hg : a.Out g) :
    a.Out (fun p x=>if c p x then f p x else g p x) := by
  obtain ⟨c',hcr,hc⟩:=hc.out false
  obtain ⟨f',hfr,hf⟩:=hf
  obtain ⟨g',hgr,hg⟩:=hg
  exact ⟨_,Computable.cond hcr hfr hgr,by intro p x; simp only [hc,hf,hg,Bool.cond_eq_ite]⟩

end UEncoding
end MinUncut.Preprocess

end OAI
