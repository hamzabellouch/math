import OAI.Computability.WeisfeilerLeman.GraphFormula

namespace OAI

universe uD uV uJ uK uL uT

namespace WLTime.Marking
variable {D : Type uD} {V : Type uV} {p : D → Prop} {count : V → ℕ}

def rectangleAdj (R : D → D → Prop) (c : D → ℕ) (d e : D) (i j : ℕ) : Prop :=
  p d ∧ p e ∧ i ≤ c d ∧ j ≤ c e ∧
    ((i=0 ∧ j=0 ∧ R d e) ∨ (i=0 ∧ j≠0 ∧ d=e) ∨ (i≠0 ∧ j=0 ∧ d=e))

 theorem decodeSlots_adj (e : {d // p d} ≃ V) (G : SimpleGraph V)
    (R : D → D → Prop) (c : D → ℕ)
    (hc : ∀d : {d // p d},count (e d)=c d.val)
    (hR : ∀d f : {d // p d},G.Adj (e d) (e f) ↔ R d.val f.val)
    (L q : ℕ) (d f : D) (i j : Fin L) :
    (rawGraph G (decodeSlots (count:=count) e L q)).Adj (some (.inl (d,i))) (some (.inl (f,j))) ↔
      rectangleAdj (p:=p) R c d f i.val j.val := by
  classical
  by_cases hd : p d
  · by_cases hf : p f
    · have heq : e ⟨d,hd⟩=e ⟨f,hf⟩ ↔ d=f := by
        rw [e.injective.eq_iff,Subtype.mk.injEq]
      have hadj := hR ⟨d,hd⟩ ⟨f,hf⟩
      have hcd := hc ⟨d,hd⟩
      have hcf := hc ⟨f,hf⟩
      by_cases hi : i.val=0 <;> by_cases hj : j.val=0
      · simpa [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,slotAdj,rectangleAdj] using hadj
      · by_cases hle : j.val-1<c f
        · have h : j.val≤c f := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcf,hle,slotAdj,rectangleAdj,h,heq]
        · have h : ¬j.val≤c f := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcf,hle,rectangleAdj,h]
      · by_cases hle : i.val-1<c d
        · have h : i.val≤c d := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hle,slotAdj,rectangleAdj,h,heq]
        · have h : ¬i.val≤c d := by omega
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hle,rectangleAdj,h]
      · by_cases hli : i.val-1<c d <;> by_cases hlj : j.val-1<c f <;>
          simp [rawGraph,rawAdj,decodeSlots,hd,hf,hi,hj,hcd,hcf,hli,hlj,rectangleAdj,slotAdj]
    · simp [rawGraph,rawAdj,decodeSlots,hd,hf,rectangleAdj]
  · simp [rawGraph,rawAdj,decodeSlots,hd,rectangleAdj]
end WLTime.Marking

namespace WLTime.NatCode
namespace Expr
variable {J : Type uJ}
def add (a b : Expr J) : Expr J := .binary .add a b
def mul (a b : Expr J) : Expr J := .binary .mul a b
@[simp] theorem add_eval (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (a.add b).eval σ w=a.eval σ w+b.eval σ w := rfl
@[simp] theorem mul_eval (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (a.mul b).eval σ w=a.eval σ w*b.eval σ w := rfl
end Expr
namespace Predicate
variable {J : Type uJ}
def le (a b : Expr J) : Predicate J := (Predicate.lt b a).neg
@[simp] theorem le_holds (a b : Expr J) (σ : J → ℕ) (w : List Bool) :
    (le a b).Holds σ w ↔ a.eval σ w≤b.eval σ w := by
  exact Nat.not_lt

def rectangular (p q R same : Predicate J) (a b i j : Expr J) : Predicate J :=
  p.conj (q.conj ((le i a).conj ((le j b).conj
    (((Predicate.eq i (Expr.const 0)).conj ((Predicate.eq j (Expr.const 0)).conj R)).disj
      (((Predicate.eq i (Expr.const 0)).conj ((Predicate.eq j (Expr.const 0)).neg.conj same)).disj
        ((Predicate.eq i (Expr.const 0)).neg.conj ((Predicate.eq j (Expr.const 0)).conj same)))))))
 theorem rectangular_holds (p q R same : Predicate J) (a b i j : Expr J)
    (σ : J → ℕ) (w : List Bool) :
    (rectangular p q R same a b i j).Holds σ w ↔
      p.Holds σ w ∧ q.Holds σ w ∧ i.eval σ w≤a.eval σ w ∧ j.eval σ w≤b.eval σ w ∧
        ((i.eval σ w=0 ∧ j.eval σ w=0 ∧ R.Holds σ w) ∨
          (i.eval σ w=0 ∧ j.eval σ w≠0 ∧ same.Holds σ w) ∨
          (i.eval σ w≠0 ∧ j.eval σ w=0 ∧ same.Holds σ w)) := by
  simp only [rectangular,Holds,disj,Expr.eval,le,not_and_or,not_not,Nat.not_lt]
  tauto
end Predicate
end WLTime.NatCode

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q K : ℕ)
open scoped Classical
noncomputable def coefficient : ℕ := (instanceData M d q []).rectCoefficient K

variable {J : Type uJ}
noncomputable def countExpr (N : Expr J) (t : BlockTag M d q K) (a b : Expr J) : Expr J :=
  ((b.add (N.mul (a.add (N.mul (Expr.const (Fintype.equivFin _ t).val))))).add (Expr.const 1)).mul
    (((Expr.const (coefficient M d q K)).mul (N.mul N)).add (Expr.const 1))

 theorem countExpr_correct (N : Expr J) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t : BlockTag M d q K) (a b : Expr J)
    (x y : Fin w.length) (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (countExpr M d q K N t a b).eval σ w=
      ConsistencyData.mixedCode K t x y*((instanceData M d q w).rectCoefficient K*w.length^2+1) := by
  simp only [countExpr,Expr.mul_eval,Expr.add_eval,Expr.eval,hN,ha,hb,
    ConsistencyData.mixedCode,coefficient,pow_two]
  rfl

noncomputable def sameRect (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) : Predicate J :=
  (Predicate.truth (decide (t=u ∧ v=z))).conj ((Predicate.eq a c).conj (Predicate.eq b e))

 theorem sameRect_correct (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (x y l h : Fin w.length)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val)
    (hc : c.eval σ w=l.val) (he : e.eval σ w=h.val) :
    (sameRect M d q K t u v z a b c e).Holds σ w ↔
      (t,v,x,y)=(u,z,l,h) := by
  simp only [sameRect,Predicate.Holds,decide_eq_true_eq,ha,hb,hc,he,Fin.val_inj,Prod.mk.injEq]
  tauto

noncomputable def slotPredicate (N : Expr J) (ε : F₂) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b i c e j : Expr J) : Predicate J :=
  Predicate.rectangular (validity M d q N K ε t v a b) (validity M d q N K ε u z c e)
    (adjacent M d q N K t u v z a b c e) (sameRect M d q K t u v z a b c e)
    (countExpr M d q K N t a b) (countExpr M d q K N u c e) i j

 theorem slotPredicate_correct (N : Expr J) (hK : 0<K) (hr : 1≤d+q)
    (ε : F₂) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (t u : BlockTag M d q K) (v z : Values M d q K) (a b i c e j : Expr J)
    (x y l h : Fin w.length) (s t' : Fin ((instanceData M d q w).slotLimit K)) (pad : ℕ)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hi : i.eval σ w=s.val)
    (hc : c.eval σ w=l.val) (he : e.eval σ w=h.val) (hj : j.eval σ w=t'.val) :
    (slotPredicate M d q K N ε t u v z a b i c e j).Holds σ w ↔
      ((instanceData M d q w).rectangularGraph K hK hr ε pad).Adj
        (some (.inl ((t,v,x,y),s))) (some (.inl ((u,z,l,h),t'))) := by
  let I := instanceData M d q w
  have hn (f : {f : I.Rect K // I.RectValid K ε f}) :
      I.spacedCount K (I.rectVertexEquiv K hK hr ε f).1=
        ConsistencyData.mixedCode K f.val.1 f.val.2.2.1 f.val.2.2.2*(I.rectCoefficient K*w.length^2+1) := by
    change ConsistencyData.rawCode K (ConsistencyData.makeBlock K f.val.1 f.val.2.2.1 f.val.2.2.2)*_= _
    rw [ConsistencyData.rawCode_make]
  have hR (f g : {f : I.Rect K // I.RectValid K ε f}) :
      (I.valuationGraph K ε).Adj (I.rectVertexEquiv K hK hr ε f) (I.rectVertexEquiv K hK hr ε g) ↔
        I.RawAdjacent K (I.rectEquiv K f.val) (I.rectEquiv K g.val) :=
    I.descriptor_adjacent K hK hr ε _ _
  unfold ConsistencyData.rectangularGraph ConsistencyData.slots
  erw [Marking.decodeSlots_adj (I.rectVertexEquiv K hK hr ε) (I.valuationGraph K ε)
    (fun f g => I.RawAdjacent K (I.rectEquiv K f) (I.rectEquiv K g))
    (fun f => ConsistencyData.mixedCode K f.1 f.2.2.1 f.2.2.2*(I.rectCoefficient K*w.length^2+1))
    hn hR]
  simp only [slotPredicate,Predicate.rectangular_holds,Marking.rectangleAdj,
    validity_correct M d q N K ε σ w hN _ _ _ _ _ _ ha hb,
    validity_correct M d q N K ε σ w hN _ _ _ _ _ _ hc he,
    sameRect_correct M d q K _ _ _ _ _ _ _ _ σ w _ _ _ _ ha hb hc he,
    countExpr_correct M d q K N σ w hN _ _ _ _ _ ha hb,
    countExpr_correct M d q K N σ w hN _ _ _ _ _ hc he,hi,hj]
  dsimp only [ConsistencyData.RectValid,ConsistencyData.rectEquiv,I]
  apply and_congr_right
  intro ht
  apply and_congr_right
  intro hu
  rw [adjacent_correct M d q N K σ w hN t u v z a b c e x y l h ha hb hc he ht.1 hu.1]
  rfl
end WLTime.OneTape.Symbolic

namespace WLTime.UnaryPrograms
open TypedStack
variable {K : Type uK} [DecidableEq K]
 theorem countdown_indexed (c : Code K Bool) (s : ℕ → Stacks K Bool) (B n i : ℕ)
    (hc : ∀j<n,∃t≤B,c.Exec (s (i+j)) t (s (i+j+1))) :
    ∃t≤n*(B+3)+1,
      (Code.loop (Code.nonempty (.inl 0)) (.seq (c.relabel Sum.inr) (.pop (.inl 0))) :
        Code (Fin 2 ⊕ K) Bool).Exec (Sum.elim (extra n) (s i)) t (Sum.elim (extra 0) (s (i+n))) := by
  induction n generalizing i with
  | zero => exact ⟨1,by omega,.loop_false (by simp [Code.nonempty,tops,extra,numeral])⟩
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := hc 0 (by omega)
    simp only [Nat.add_zero] at he
    have hb := Code.Exec.seq (Code.relabel_inr_exec he (extra (n+1))) (Code.Exec.pop _ (.inl 0))
    rw [extra_succ_update] at hb
    obtain ⟨v,hv,hr⟩ := ih (i+1) (fun j hj => by simpa only [Nat.add_assoc,Nat.add_comm 1] using hc (j+1) (by omega))
    have hh := Code.Exec.loop_true (p:=Code.nonempty (.inl 0))
      (by simp [Code.nonempty,tops,extra,numeral]) hb hr
    refine ⟨u+2+v+1,by nlinarith,?_⟩
    convert hh using 1
    congr 2
    omega

 theorem repeat_indexed (base : K) (c : Code K Bool) (s : ℕ → Stacks K Bool) (B n : ℕ)
    (hc : ∀j<n,∃t≤B,c.Exec (s j) t (s (j+1))) (hb : s 0 base=numeral n) :
    ∃t≤n*(B+15)+3,(repeatN base c).Exec (Sum.elim (extra 0) (s 0)) t (Sum.elim (extra 0) (s n)) := by
  have hf := Code.copy_exec (.inr base : Fin 2 ⊕ K) (.inl 0) (.inl 1)
    (by simp) (by simp) (by simp) false (Sum.elim (extra 0) (s 0)) (by simp [extra])
  have he : Function.update (Sum.elim (extra 0) (s 0)) (.inl 0)
      (Sum.elim (extra 0) (s 0) (.inr base)++Sum.elim (extra 0) (s 0) (.inl 0))=Sum.elim (extra n) (s 0) := by
    funext i; cases i with
    | inl j => fin_cases j <;> simp [extra,numeral,hb]
    | inr j => simp
  rw [he] at hf
  obtain ⟨t,ht,hr⟩ := countdown_indexed c s B n 0 (by simpa only [Nat.zero_add])
  simp only [Nat.zero_add] at hr
  refine ⟨_,?_,Code.Exec.seq hf hr⟩
  simp only [Sum.elim_inr,hb,numeral_length]
  nlinarith
end WLTime.UnaryPrograms

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]
 theorem repeat_indexed (base : K) (p : Program K) (s : ℕ → Stacks K Bool) (B n : ℕ)
    (hc : ∀j<n,∃t≤B,p.Exec (s j) t (s (j+1))) (hb : s 0 base=UnaryPrograms.numeral n) :
    ∃t≤n*(B+15)+3,(repeatN base p).Exec (s 0) t (s n) := by
  obtain ⟨t,ht,he⟩ := UnaryPrograms.repeat_indexed (.inr base : Fin p.scratch ⊕ K) p.code
    (fun i => p.ambient (s i)) B n hc hb
  refine ⟨t,ht,?_⟩
  apply Code.relabel_exec_of_maps _ (Equiv.injective _) he
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro k; cases k with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i <;> rfl
  · intro l hl; exact False.elim (hl ((merge 2 p.scratch).symm l) (Equiv.apply_symm_apply _ l))
end WLTime.TypedStack.Program

namespace WLTime.NatCode
open TypedStack UnaryPrograms
universe u

inductive Writer : Type u → Type (u+1) where
  | emit {K : Type u} (p : Predicate K) : Writer K
  | seq {K : Type u} (a b : Writer K) : Writer K
  | loop {K : Type u} (n : Expr K) (body : Writer (Option K)) : Writer K

namespace Writer
variable {K : Type u}

def eval {K : Type u} : Writer K → (K → ℕ) → List Bool → List Bool
  | .emit p,σ,w => [decide (p.Holds σ w)]
  | .seq a b,σ,w => a.eval σ w++b.eval σ w
  | .loop n body,σ,w => (List.range (n.eval σ w)).flatMap (fun i => body.eval (Option.elim' i σ) w)

def depth {K : Type u} : Writer K → ℕ
  | .emit _ => 0
  | .seq a b => max a.depth b.depth
  | .loop _ body => body.depth+1

def charge {K : Type u} : Writer K → ℕ
  | .emit p => 4*p.code.charge+20
  | .seq a b => a.charge+b.charge
  | .loop n body => n.charge+body.charge+100

def Safe {K : Type u} : Writer K → (K → ℕ) → List Bool → ℕ → Prop
  | .emit p,σ,w,B => p.Bounded σ w B
  | .seq a b,σ,w,B => a.Safe σ w B ∧ b.Safe σ w B
  | .loop n body,σ,w,B => n.Bounded σ w B ∧ ∀i<n.eval σ w,body.Safe (Option.elim' i σ) w B

def compile {K : Type u} : Writer K → {L : Type uL} → [DecidableEq L] → (K → L) → L → L → Program L
  | .emit p,_,_,ρ,word,out => Program.allocate
    (Program.seq (p.code.compile (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1)))
      (Program.seq (Program.ofCode (.pushDyn (.inr out) (fun z => z (.inl 0)==some true)))
        (Program.clear (.inl 0))))
  | .seq a b,_,_,ρ,word,out => Program.seq (a.compile ρ word out) (b.compile ρ word out)
  | .loop n body,_,_,ρ,word,out => Program.allocate
    (Program.seq (n.compile (Sum.inr ∘ ρ) (.inr word) (.inl (1 : Fin 2)))
      (Program.seq (Program.repeatN (.inl 1)
        (Program.seq (body.compile (Option.elim' (.inl 0) (Sum.inr ∘ ρ)) (.inr word) (.inr out))
          (Program.push (.inl 0) true)))
        (Program.seq (Program.clear (.inl 0)) (Program.clear (.inl 1)))))

 theorem numeral_bool_head (p : Prop) [Decidable p] :
    ((numeral (if p then 1 else 0)).head?==some true)=decide p := by by_cases hp:p <;> simp [hp,numeral]

 theorem emit_exec {L : Type uL} [DecidableEq L] (p : Predicate K) (ρ : K → L) (word out : L)
    (_how : out≠word) (_hor : ∀k,out≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (hp : p.Bounded σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀k,s (ρ k)=numeral (σ k)) (hw : s word=w) :
    ∃t≤(4*p.code.charge+20)*(B+1)^2,
      ((Writer.emit p).compile ρ word out).Exec s t
        (Function.update s out (decide (p.Holds σ w)::s out)) := by
  let z : Stacks (Fin 1 ⊕ L) Bool := Sum.elim (fun _ => []) s
  obtain ⟨t,ht,he⟩ := p.code.compile_exec (Sum.inr ∘ ρ) (.inr word) (.inl (0 : Fin 1))
    (by simp) (fun _ => by simp) σ w (2*B+1) (p.code_bounded σ w B hp) (by omega) z
    (fun k => hs k) hw (by simp [z])
  let mid := Function.update z (.inl (0 : Fin 1)) (numeral (p.code.eval σ w))
  have hb := Program.ofCode_exec (Code.Exec.pushDyn mid (.inr out) (fun v => v (.inl 0)==some true))
  have hc := Program.clear_exec (.inl (0 : Fin 1))
    (Function.update mid (.inr out) ((tops mid (.inl 0)==some true)::mid (.inr out)))
  have hh := Program.seq_exec he (Program.seq_exec hb hc)
  have hout : Function.update
      (Function.update mid (.inr out) ((tops mid (.inl 0)==some true)::mid (.inr out))) (.inl 0) []=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s out (decide (p.Holds σ w)::s out)) := by
    funext j; cases j with
    | inl i => have hi:i=0 := Subsingleton.elim _ _; subst i; simp
    | inr j => simp only [mid,z,tops,p.code_eval,numeral_bool_head,
        Function.update_of_ne Sum.inr_ne_inl,Function.update_apply,Sum.inr.injEq,
        Sum.elim_inr,ite_true]
  rw [hout] at hh
  refine ⟨_,?_,Program.local_exec hh⟩
  simp only [mid,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length]
  have hv := p.code_le_one σ w
  nlinarith [Nat.zero_le (B*B)]

 theorem compile_exec (p : Writer K) {L : Type uL} [DecidableEq L] (ρ : K → L) (word out : L)
    (how : out≠word) (hor : ∀k,out≠ρ k) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (hp : p.Safe σ w B) (hwB : w.length≤B) (s : Stacks L Bool)
    (hs : ∀k,s (ρ k)=numeral (σ k)) (hw : s word=w) :
    ∃t≤p.charge*(B+1)^(p.depth+2),(p.compile ρ word out).Exec s t
      (Function.update s out ((p.eval σ w).reverse++s out)) := by
  induction p generalizing L with
  | emit p => simpa only [compile,depth,charge,eval,List.reverse_singleton,List.singleton_append] using
      emit_exec p ρ word out how hor σ w B hp hwB s hs hw
  | seq a b iha ihb =>
    obtain ⟨t,ht,h1⟩ := iha ρ word out how hor σ hp.1 s hs hw
    obtain ⟨v,hv,h2⟩ := ihb ρ word out how hor σ hp.2
      (Function.update s out ((a.eval σ w).reverse++s out))
      (fun k => by simpa only [Function.update_of_ne (hor k).symm] using hs k)
      (by simpa only [Function.update_of_ne how.symm] using hw)
    have hh := Program.seq_exec h1 h2
    refine ⟨t+v,?_,?_⟩
    · have hpa := Nat.pow_le_pow_right (by omega : 1≤B+1) (Nat.add_le_add_right (Nat.le_max_left a.depth b.depth) 2)
      have hpb := Nat.pow_le_pow_right (by omega : 1≤B+1) (Nat.add_le_add_right (Nat.le_max_right a.depth b.depth) 2)
      calc
        t+v ≤ a.charge*(B+1)^(a.depth+2)+b.charge*(B+1)^(b.depth+2) := Nat.add_le_add ht hv
        _ ≤ (a.charge+b.charge)*(B+1)^(max a.depth b.depth+2) := by nlinarith
    · simpa only [compile,eval,List.reverse_append,List.append_assoc,Function.update_self,Function.update_idem] using hh
  | loop n body ih =>
    let z : Stacks (Fin 2 ⊕ L) Bool := Sum.elim (fun _ => []) s
    let N := n.eval σ w
    let words (i : ℕ) := (List.range i).flatMap (fun j => body.eval (Option.elim' j σ) w)
    let st (i : ℕ) : Stacks (Fin 2 ⊕ L) Bool :=
      Function.update (Function.update (Function.update z (.inl 1) (numeral N)) (.inl 0) (numeral i))
        (.inr out) ((words i).reverse++s out)
    have hn := n.eval_le σ w B hp.1
    obtain ⟨t,ht,h0⟩ := n.compile_exec (Sum.inr ∘ ρ) (.inr word) (.inl (1 : Fin 2))
      (by simp) (fun _ => by simp) σ w B hp.1 hwB z (fun k => hs k) hw (by simp [z])
    have hs0 : st 0=Function.update z (.inl 1) (numeral N) := by
      funext j; cases j with
      | inl j =>
        by_cases hj : j=0
        · subst j
          simp only [st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral,
            List.replicate_zero,Function.update_of_ne (by simp : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ L)≠.inl 1),
            z,Sum.elim_inl]
        · have hj' : j=1 := by omega
          subst j
          simp only [st,Function.update_of_ne Sum.inl_ne_inr,
            Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0),Function.update_self]
      | inr j =>
        simp only [st,z,words,List.range_zero,List.flatMap_nil,List.reverse_nil,
          List.nil_append,Function.update_of_ne Sum.inr_ne_inl,Function.update_apply,
          Sum.inr.injEq,Sum.elim_inr]
        split_ifs with h
        · subst j; rfl
        · rfl
    rw [← hs0] at h0
    let step := Program.seq
      (body.compile (Option.elim' (.inl (0 : Fin 2)) (Sum.inr ∘ ρ)) (.inr word) (.inr out))
      (Program.push (.inl 0) true)
    have hρ (k) : (Sum.inr (ρ k) : Fin 2 ⊕ L)≠.inr out := by
      intro h; exact hor k (Sum.inr.inj h).symm
    have hword : (Sum.inr word : Fin 2 ⊕ L)≠.inr out := by
      intro h; exact how (Sum.inr.inj h).symm
    have steps : ∀j<N,∃v≤body.charge*(B+1)^(body.depth+2)+2,step.Exec (st j) v (st (j+1)) := by
      intro j hj
      obtain ⟨v,hv,he⟩ := ih (Option.elim' (.inl (0 : Fin 2)) (Sum.inr ∘ ρ)) (.inr word) (.inr out)
        (by simpa using how) (fun k => by cases k <;> simp [hor]) (Option.elim' j σ) (hp.2 j hj) (st j)
        (fun k => by cases k with
          | none => simp only [Option.elim',st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self]
          | some k => simpa only [Option.elim',st,Function.comp_apply,Function.update_of_ne (hρ k),
              Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hs k)
        (by simpa only [st,Function.update_of_ne hword,Function.update_of_ne Sum.inr_ne_inl,z,Sum.elim_inr] using hw)
      have hi := Program.push_exec (.inl (0 : Fin 2)) true
        (Function.update (st j) (.inr out) ((body.eval (Option.elim' j σ) w).reverse++st j (.inr out)))
      have hh := Program.seq_exec he hi
      refine ⟨v+2,by omega,?_⟩
      convert hh using 1
      funext k; cases k with
      | inl k => fin_cases k <;> simp [st,numeral,List.replicate_succ]
      | inr k => simp [st,words,List.range_succ,List.flatMap_append,List.reverse_append,List.append_assoc]
    obtain ⟨v,hv,h1⟩ := Program.repeat_indexed (.inl (1 : Fin 2)) step st
      (body.charge*(B+1)^(body.depth+2)+2) N steps (by simp [st])
    have h2 := Program.clear_exec (.inl (0 : Fin 2)) (st N)
    have h3 := Program.clear_exec (.inl (1 : Fin 2)) (Function.update (st N) (.inl 0) [])
    have hh := Program.seq_exec h0 (Program.seq_exec h1 (Program.seq_exec h2 h3))
    have hout : Function.update (Function.update (st N) (.inl 0) []) (.inl 1) []=
        Sum.elim (fun _ : Fin 2 => []) (Function.update s out (((Writer.loop n body).eval σ w).reverse++s out)) := by
      funext j; cases j with
      | inl j => fin_cases j <;> simp
      | inr j => simp only [st,z,eval,words,N,Function.update_of_ne Sum.inr_ne_inl,
          Function.update_apply,Sum.inr.injEq,Sum.elim_inr]
    rw [hout] at hh
    refine ⟨_,?_,Program.local_exec hh⟩
    simp only [st,Function.update_of_ne Sum.inl_ne_inr,Function.update_self,numeral_length,
      Function.update_of_ne (by simp : (Sum.inl (1 : Fin 2) : Fin 2 ⊕ L)≠.inl 0)]
    change t+(v+(3*N+1+(3*N+1)))≤(n.charge+body.charge+100)*(B+1)^(body.depth+1+2)
    have hexp : body.depth+1+2=(body.depth+2)+1 := by omega
    rw [hexp,pow_succ]
    have hpow : (B+1)^2≤(B+1)^(body.depth+2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hone : 1≤(B+1)^(body.depth+2) := Nat.one_le_pow _ _ (by omega)
    dsimp [N] at hv ⊢
    nlinarith [Nat.mul_le_mul_left n.charge hpow,
      Nat.mul_le_mul_right (body.charge*(B+1)^(body.depth+2)+17) hn,
      Nat.mul_le_mul_left B hone]
end Writer
end WLTime.NatCode

namespace WLTime.NatCode
namespace Expr
variable {K : Type uK} {J : Type uJ}
def rename (f : K → J) (e : Expr K) : Expr J := e.bind (Expr.var ∘ f)
@[simp] theorem rename_eval (f : K → J) (e : Expr K) (σ : J → ℕ) (w : List Bool) :
    (e.rename f).eval σ w=e.eval (σ ∘ f) w := by simp only [rename,bind_eval,eval,Function.comp_def]
 theorem rename_bounded (f : K → J) (e : Expr K) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (e.rename f).Bounded σ w B ↔ e.Bounded (σ ∘ f) w B := by
  induction e with
  | const | var => rfl
  | binary op a b ha hb =>
    change ((a.rename f).Bounded σ w B ∧ (b.rename f).Bounded σ w B ∧
      op.eval ((a.rename f).eval σ w) ((b.rename f).eval σ w)≤B) ↔ _
    rw [ha,hb,rename_eval,rename_eval]
    rfl
  | bit a ha =>
    exact and_congr ha Iff.rfl

end Expr
namespace Writer
variable {K : Type uK}
def empty : Writer K := .loop (.const 0) (.emit (.truth false))
@[simp] theorem empty_eval (σ : K → ℕ) (w : List Bool) : (empty : Writer K).eval σ w=[] := rfl
@[simp] theorem empty_depth : (empty : Writer K).depth=1 := rfl
 theorem empty_safe (σ : K → ℕ) (w : List Bool) (B : ℕ) : (empty : Writer K).Safe σ w B := by
  exact ⟨Nat.zero_le _,fun i hi => (Nat.not_lt_zero i hi).elim⟩
def each {T : Type uT} (l : List T) (f : T → Writer K) : Writer K := l.foldr (fun t p => .seq (f t) p) empty
@[simp] theorem each_eval {T : Type uT} (l : List T) (f : T → Writer K) (σ : K → ℕ) (w : List Bool) :
    (each l f).eval σ w=l.flatMap (fun t => (f t).eval σ w) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    change (f t).eval σ w++(each l f).eval σ w=_
    rw [ih,List.flatMap_cons]
 theorem each_safe {T : Type uT} (l : List T) (f : T → Writer K) (σ : K → ℕ) (w : List Bool) (B : ℕ)
    (h : ∀t∈l,(f t).Safe σ w B) : (each l f).Safe σ w B := by
  induction l with
  | nil => exact empty_safe σ w B
  | cons t l ih => exact ⟨h t (by simp),ih (fun t ht => h t (by simp [ht]))⟩
 theorem each_depth_le {T : Type uT} (l : List T) (f : T → Writer K) (b : ℕ) (hb : 1≤b)
    (h : ∀t∈l,(f t).depth≤b) : (each l f).depth≤b := by
  induction l with
  | nil => exact hb
  | cons t l ih => exact max_le (h t (by simp)) (ih (fun t ht => h t (by simp [ht])))

def grid (N L : Expr K) (body : Writer (Option (Option (Option K)))) : Writer K :=
  .loop N (.loop (N.rename some) (.loop (L.rename (some ∘ some)) body))
 theorem grid_eval (N L : Expr K) (body : Writer (Option (Option (Option K))))
    (σ : K → ℕ) (w : List Bool) :
    (grid N L body).eval σ w=(List.range (N.eval σ w)).flatMap (fun a =>
      (List.range (N.eval σ w)).flatMap (fun b =>
        (List.range (L.eval σ w)).flatMap (fun i => body.eval
          (Option.elim' i (Option.elim' b (Option.elim' a σ))) w))) := by
  simp only [grid,eval,Expr.rename_eval,Function.comp_def,Option.elim'_some]
 theorem grid_safe (N L : Expr K) (body : Writer (Option (Option (Option K))))
    (σ : K → ℕ) (w : List Bool) (B : ℕ) (hN : N.Bounded σ w B) (hL : L.Bounded σ w B)
    (hb : ∀a<N.eval σ w,∀b<N.eval σ w,∀i<L.eval σ w,
      body.Safe (Option.elim' i (Option.elim' b (Option.elim' a σ))) w B) :
    (grid N L body).Safe σ w B := by
  refine ⟨hN,fun a ha => ⟨?_,fun b hb' => ⟨?_,fun i hi => ?_⟩⟩⟩
  · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hN
  · simpa only [Expr.rename_bounded,Function.comp_def,Option.elim'_some] using hL
  · simp only [Expr.rename_eval,Function.comp_def,Option.elim'_some] at hb' hi
    exact hb a ha b hb' i hi
@[simp] theorem grid_depth (N L : Expr K) (body : Writer (Option (Option (Option K)))) :
    (grid N L body).depth=body.depth+3 := by simp only [grid,depth]
end Writer
end WLTime.NatCode

end OAI
