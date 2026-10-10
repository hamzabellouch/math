import OAI.Computability.WeisfeilerLeman.Simulation

namespace OAI

universe uJ uT uP uE uA uB uA' uB' uV uW uU

namespace WLTime.OneTape
open NatCode
variable (M : OneTape) {J : Type uJ}
 theorem inputPredicate_bounded (f : M.Cell) (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) : (M.inputPredicate f a).Bounded σ w B := by
  simp only [inputPredicate,Predicate.bounded_disj,Predicate.Bounded,Expr.Bounded]
  exact ⟨⟨⟨ha,trivial⟩,ha,trivial⟩,⟨⟨⟨ha,Nat.zero_le _⟩,trivial⟩,⟨ha,Nat.zero_le _⟩,trivial⟩⟩
end WLTime.OneTape

namespace WLTime.Compression
open NatCode
namespace FormalName
variable {T : Type uT} {J : Type uJ}
def Bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) (n : FormalName T J) : Prop :=
  n.first.Bounded σ w B ∧ n.second.Bounded σ w B
 theorem equal_bounded (σ : J → ℕ) (w : List Bool) (B : ℕ) (a b : FormalName T J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) : (a.equal b).Bounded σ w B := by
  exact ⟨trivial,⟨ha.1,hb.1⟩,ha.2,hb.2⟩
end FormalName
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} {J : Type uJ} (I : ConsistencyData (r+1) m P E)
variable (D : E → Fin (r+1) → Expr J → Predicate J) (Q : E → Fin (r+1) → Expr J → Expr J)

 theorem blockPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J)
    (hD : ∀e i,(D e i a).Bounded σ w B ∧ (D e i b).Bounded σ w B) :
    (blockPredicate D K t a b).Bounded σ w B := by
  rcases t with ⟨i,t|l⟩
  · cases t with
    | inl p => exact ⟨trivial,trivial⟩
    | inr e => exact ⟨(hD e.1 i).1,(hD e.1 (finRotate (r+1) i)).2⟩
  · exact ⟨(hD l.1 i).1,(hD l.1 (finRotate (r+1) i)).2⟩

 theorem validPredicate_bounded (K : ℕ) (ε : F₂) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (v : I.TagValues K) (a b : Expr J)
    (hD : ∀e i,(D e i a).Bounded σ w B ∧ (D e i b).Bounded σ w B) :
    (I.validPredicate D K ε t v a b).Bounded σ w B :=
  ⟨blockPredicate_bounded D K σ w B t a b hD,trivial⟩

 theorem formalFootprint_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Expr J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hQ : ∀e i,(Q e i a).Bounded σ w B ∧ (Q e i b).Bounded σ w B) :
    ∀n∈I.formalFootprint Q K t a b,n.Bounded σ w B := by
  rcases t with ⟨i,t|l⟩
  · intro n hn
    simp only [formalFootprint,List.mem_cons,List.not_mem_nil,or_false] at hn
    subst n
    exact ⟨ha,hb⟩
  · intro n hn
    simp only [formalFootprint,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl|rfl|rfl
    · exact ⟨ha,hb⟩
    · unfold FormalName.Bounded matchCode
      split_ifs
      · exact ⟨(hQ l.1 i).1,(hQ l.1 (finRotate (r+1) i)).2⟩
      · exact ⟨ha,hb⟩
    · exact ⟨ha,Nat.zero_le _⟩
    · exact ⟨hb,Nat.zero_le _⟩

 theorem overlapPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (hl : ∀a∈l,a.Bounded σ w B) (hs : ∀b∈s,b.Bounded σ w B) :
    (overlapPredicate K l s).Bounded σ w B := by
  rw [overlapPredicate,Predicate.bounded_any]
  intro p hp
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  exact FormalName.equal_bounded σ w B a b (hl a ha) (hs b hb)

 theorem agreePredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ) (v u : I.TagValues K)
    (l s : List (FormalName (Tag (r:=r) (P:=P) (E:=E) K) J))
    (hl : ∀a∈l,a.Bounded σ w B) (hs : ∀b∈s,b.Bounded σ w B) :
    (I.agreePredicate K v u l s).Bounded σ w B := by
  rw [agreePredicate,Predicate.bounded_all]
  intro p hp
  obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
  exact ⟨FormalName.equal_bounded σ w B a b (hl a ha) (hs b hb),trivial⟩

 theorem adjacencyPredicate_bounded (K : ℕ) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (t u : BlockTag (r:=r) (P:=P) (E:=E) K) (v z : I.TagValues K) (a b c d : Expr J)
    (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) (hc : c.Bounded σ w B) (hd : d.Bounded σ w B)
    (hQ : ∀e i,(Q e i a).Bounded σ w B ∧ (Q e i b).Bounded σ w B ∧
      (Q e i c).Bounded σ w B ∧ (Q e i d).Bounded σ w B) :
    (I.adjacencyPredicate Q K t u v z a b c d).Bounded σ w B := by
  have hl := I.formalFootprint_bounded Q K σ w B t a b ha hb (fun e i => ⟨(hQ e i).1,(hQ e i).2.1⟩)
  have hs := I.formalFootprint_bounded Q K σ w B u c d hc hd (fun e i => (hQ e i).2.2)
  exact ⟨⟨trivial,⟨ha,hc⟩,hb,hd⟩,overlapPredicate_bounded K σ w B _ _ hl hs,
    I.agreePredicate_bounded K σ w B v z _ _ hl hs⟩
end ConsistencyData
end WLTime.Compression

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q : ℕ)

abbrev Node := Schematic.Node (Tableau.Gate M.Cell) (BoxTableau.Label M.Cell d (q+1))
abbrev Edge := Schematic.Edge (BoxTableau.Label M.Cell d (q+1)) (M.Cell ⊕ Fin q)
  {f : M.Cell // M.letterAccepting f}

noncomputable def schema (w : List Bool) : Schematic (d+q+1) w.length (Tableau.Gate M.Cell)
    (BoxTableau.Label M.Cell d (q+1)) (M.Cell ⊕ Fin q) {f : M.Cell // M.letterAccepting f} :=
  BoxTableau.schematic (d:=d) (q:=q) M.localRule (M.inputCell w) M.blankCell M.letterAccepting

noncomputable def instanceData (w : List Bool) : ConsistencyData (d+q+1) w.length (Node M d q) (Edge M d q) :=
  (schema M d q w).consistency

variable {J : Type uJ}
noncomputable def domain (N : Expr J) : Edge M d q → Fin (d+q+1) → Expr J → Predicate J
  | .first e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .second e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .third e,i,a => BoxTableau.Formula.labelDomain e N a i
  | .seed s,i,a => BoxTableau.Formula.seed (d:=d) (q:=q) M.inputPredicate s a i
  | .test _,i,a => BoxTableau.Formula.test (d:=d) (q:=q) N a i

def coord (N : Expr J) : Edge M d q → Fin (d+q+1) → Expr J → Expr J
  | .third e,i,a => BoxTableau.Formula.labelCoord e N a i
  | _,_,a => a

 theorem domain_correct (N : Expr J) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J) (x : Fin w.length) (ha : a.eval σ w=x.val) :
    (domain M d q N e i a).Holds σ w ↔ x∈(instanceData M d q w).domain e i := by
  classical
  cases e with
  | first e | second e | third e =>
    exact BoxTableau.Formula.labelDomain_correct e N a i σ w x hN ha
  | seed s =>
    exact BoxTableau.Formula.seed_correct (M.inputCell w) M.inputPredicate σ w
      (fun f a x hx => M.inputPredicate_correct f a σ w x hx) s a i x ha
  | test f => exact BoxTableau.Formula.test_correct (d:=d) (q:=q) M.letterAccepting f N a i σ w x hN ha

 theorem coord_correct (N : Expr J) (σ : J → ℕ) (w : List Bool) (hN : N.eval σ w=w.length)
    (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J) (x : Fin w.length)
    (hx : x∈(instanceData M d q w).domain e i) (ha : a.eval σ w=x.val) :
    (coord M d q N e i a).eval σ w=((instanceData M d q w).coord e i ⟨x,hx⟩).val := by
  cases e with
  | first | second | seed | test => exact ha
  | third e => exact BoxTableau.Formula.labelCoord_correct e N a i σ w x hN ha

abbrev BlockTag (K : ℕ) := ConsistencyData.BlockTag (r:=d+q) (P:=Node M d q) (E:=Edge M d q) K
abbrev Values (K : ℕ) := (instanceData M d q []).TagValues K

 theorem fixedLegal_iff (K : ℕ) (ε : F₂) (w : List Bool) (t : BlockTag M d q K)
    (v : Values M d q K) :
    (instanceData M d q []).FixedLegal K ε t v ↔ (instanceData M d q w).FixedLegal K ε t v := by
  unfold ConsistencyData.FixedLegal ConsistencyData.fixedForm ConsistencyData.fixedBias
  rcases t with ⟨i,t|⟨e,j⟩⟩
  · rfl
  · cases e <;> rfl

noncomputable def validity (N : Expr J) (K : ℕ) (ε : F₂) (t : BlockTag M d q K)
    (v : Values M d q K) (a b : Expr J) : Predicate J :=
  (instanceData M d q []).validPredicate (domain M d q N) K ε t v a b

noncomputable def adjacent (N : Expr J) (K : ℕ) (t u : BlockTag M d q K)
    (v z : Values M d q K) (a b c e : Expr J) : Predicate J :=
  (instanceData M d q []).adjacencyPredicate (coord M d q N) K t u v z a b c e

 theorem validity_correct (N : Expr J) (K : ℕ) (ε : F₂) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t : BlockTag M d q K) (v : Values M d q K)
    (a b : Expr J) (x y : Fin w.length) (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) :
    (validity M d q N K ε t v a b).Holds σ w ↔
      (instanceData M d q w).DescriptorValid K ε (ConsistencyData.makeBlock K t x y,v) := by
  erw [(instanceData M d q w).descriptorValid_fixed]
  simp only [validity,ConsistencyData.validPredicate,Predicate.Holds,decide_eq_true_eq,
    fixedLegal_iff M d q K ε w t v]
  exact and_congr ((instanceData M d q w).blockPredicate_holds (domain M d q N) K σ w
    (domain_correct M d q N σ w hN) t a b x y ha hb) Iff.rfl

 theorem adjacent_correct (N : Expr J) (K : ℕ) (σ : J → ℕ) (w : List Bool)
    (hN : N.eval σ w=w.length) (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (x y p s : Fin w.length)
    (ha : a.eval σ w=x.val) (hb : b.eval σ w=y.val) (hc : c.eval σ w=p.val) (he : e.eval σ w=s.val)
    (ht : (instanceData M d q w).ValidBlock K (ConsistencyData.makeBlock K t x y))
    (hu : (instanceData M d q w).ValidBlock K (ConsistencyData.makeBlock K u p s)) :
    (adjacent M d q N K t u v z a b c e).Holds σ w ↔
      (instanceData M d q w).RawAdjacent K (ConsistencyData.makeBlock K t x y,v)
        (ConsistencyData.makeBlock K u p s,z) := by
  change ((instanceData M d q w).adjacencyPredicate (coord M d q N) K t u v z a b c e).Holds σ w ↔ _
  exact (instanceData M d q w).adjacencyPredicate_correct (coord M d q N) K σ w
    (coord_correct M d q N σ w hN) t u v z a b c e x y p s ha hb hc he ht hu
end WLTime.OneTape.Symbolic

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression
variable (M : OneTape) (d q : ℕ) {J : Type uJ}

 theorem domain_bounded (N : Expr J) (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) :
    (domain M d q N e i a).Bounded σ w (6*B) := by
  cases e with
  | first e | second e | third e => exact BoxTableau.Formula.labelDomain_bounded e N a i σ w B hB hN ha
  | seed s =>
    exact (BoxTableau.Formula.seed _ s a i).bounded_mono σ w
      (BoxTableau.Formula.seed_bounded M.inputPredicate s a i σ w B ha (fun f => M.inputPredicate_bounded f a σ w B ha))
      (by omega)
  | test f =>
    exact (BoxTableau.Formula.test (d:=d) (q:=q) N a i).bounded_mono σ w
      (BoxTableau.Formula.test_bounded (d:=d) (q:=q) N a i σ w B hB hN ha) (by omega : 2*B≤6*B)

 theorem coord_bounded (N : Expr J) (e : Edge M d q) (i : Fin (d+q+1)) (a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) :
    (coord M d q N e i a).Bounded σ w (6*B) := by
  cases e with
  | third e => exact BoxTableau.Formula.labelCoord_bounded e N a i σ w B hB hN ha
  | first | second | seed | test => exact a.bounded_mono σ w ha (by omega)

 theorem validity_bounded (N : Expr J) (K : ℕ) (ε : F₂) (t : BlockTag M d q K) (v : Values M d q K)
    (a b : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B) :
    (validity M d q N K ε t v a b).Bounded σ w (6*B) :=
  (instanceData M d q []).validPredicate_bounded _ K ε σ w (6*B) t v a b
    (fun e i => ⟨domain_bounded M d q N e i a σ w B hB hN ha,
      domain_bounded M d q N e i b σ w B hB hN hb⟩)

 theorem adjacent_bounded (N : Expr J) (K : ℕ) (t u : BlockTag M d q K) (v z : Values M d q K)
    (a b c e : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hN : N.Bounded σ w B) (ha : a.Bounded σ w B) (hb : b.Bounded σ w B)
    (hc : c.Bounded σ w B) (he : e.Bounded σ w B) :
    (adjacent M d q N K t u v z a b c e).Bounded σ w (6*B) :=
  (instanceData M d q []).adjacencyPredicate_bounded _ K σ w (6*B) t u v z a b c e
    (a.bounded_mono σ w ha (by omega)) (b.bounded_mono σ w hb (by omega))
    (c.bounded_mono σ w hc (by omega)) (e.bounded_mono σ w he (by omega))
    (fun f i => ⟨coord_bounded M d q N f i a σ w B hB hN ha,
      coord_bounded M d q N f i b σ w B hB hN hb,
      coord_bounded M d q N f i c σ w B hB hN hc,
      coord_bounded M d q N f i e σ w B hB hN he⟩)
end WLTime.OneTape.Symbolic

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev Rect (K : ℕ) := BlockTag (r:=r) (P:=P) (E:=E) K × I.TagValues K × Fin m × Fin m

noncomputable def rectEquiv (K : ℕ) : I.Rect K ≃ I.Descriptor K where
  toFun x := (makeBlock K x.1 x.2.2.1 x.2.2.2,x.2.1)
  invFun x := match x.1 with
    | .site i t a b => ((i,.inl t),x.2,a,b)
    | .square i l a b => ((i,.inr l),x.2,a,b)
  left_inv x := by rcases x with ⟨⟨i,t|l⟩,v,a,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨b,v⟩; cases b <;> rfl

def RectValid (K : ℕ) (ε : F₂) (v : I.Rect K) : Prop :=
  I.DescriptorValid K ε (I.rectEquiv K v)

noncomputable def rectVertexEquiv (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    {v : I.Rect K // I.RectValid K ε v} ≃ I.Vertex K ε :=
  (Equiv.subtypeEquiv (I.rectEquiv K) (fun _ => Iff.rfl)).trans (I.descriptorEquiv K hK hr ε)

variable [Fintype P] [Fintype E]
open scoped Classical

noncomputable def mixedCode (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) : ℕ :=
  (b.val+m*(a.val+m*(Fintype.equivFin _ t).val))+1

 theorem mixedCode_pos (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    0 < mixedCode (m:=m) K t a b := by unfold mixedCode; omega

 theorem mixedCode_le (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    mixedCode (m:=m) K t a b≤Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*m^2 := by
  have ht := (finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ t,a),b)).isLt
  change b.val+m*(a.val+m*(Fintype.equivFin _ t).val) < _ at ht
  unfold mixedCode
  nlinarith

 theorem mixedCode_injective (K : ℕ) :
    Function.Injective (fun x : BlockTag (r:=r) (P:=P) (E:=E) K × Fin m × Fin m =>
      mixedCode (m:=m) K x.1 x.2.1 x.2.2) := by
  rintro ⟨t,a,b⟩ ⟨u,c,d⟩ h
  have he : finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ t,a),b) =
      finProdFinEquiv (finProdFinEquiv (Fintype.equivFin _ u,c),d) := by
    apply Fin.ext
    change b.val+m*(a.val+m*(Fintype.equivFin _ t).val) = d.val+m*(c.val+m*(Fintype.equivFin _ u).val)
    simpa only [mixedCode,Nat.add_left_inj] using h
  have h1 := finProdFinEquiv.injective he
  have h2 := finProdFinEquiv.injective (congrArg Prod.fst h1)
  have ht := (Fintype.equivFin _).injective (congrArg Prod.fst h2)
  have ha : a=c := congrArg Prod.snd h2
  have hb : b=d := congrArg Prod.snd h1
  subst u; subst c; subst d; rfl

noncomputable def rawCode (K : ℕ) : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K → ℕ
  | .site i t a b => mixedCode (P:=P) (E:=E) K (i,.inl t) a b
  | .square i e a b => mixedCode (P:=P) (E:=E) K (i,.inr e) a b

 theorem rawCode_make (K : ℕ) (t : BlockTag (r:=r) (P:=P) (E:=E) K) (a b : Fin m) :
    rawCode K (makeBlock K t a b)=mixedCode K t a b := by rcases t with ⟨i,t|l⟩ <;> rfl

 theorem rawCode_injective (K : ℕ) : Function.Injective (rawCode (r:=r) (m:=m) (P:=P) (E:=E) K) := by
  intro x y h
  cases x <;> cases y
  all_goals simp only [rawCode] at h
  all_goals have he := mixedCode_injective K (a₁:=(_,_,_)) (a₂:=(_,_,_)) h
  all_goals simp only [Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at he
  all_goals first | rcases he with ⟨⟨rfl,rfl⟩,rfl,rfl⟩; rfl | tauto

 theorem rawCode_pos (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) : 0<rawCode K v := by
  cases v <;> exact mixedCode_pos (P:=P) (E:=E) K _ _ _

 theorem rawCode_le (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    rawCode K v≤Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*m^2 := by
  cases v <;> exact mixedCode_le (P:=P) (E:=E) K _ _ _

noncomputable def rectCoefficient (K : ℕ) :=
  Fintype.card (BlockTag (r:=r) (P:=P) (E:=E) K)*Fintype.card (I.TagValues K)

 theorem rect_card (K : ℕ) : Fintype.card (I.Rect K)=I.rectCoefficient K*m^2 := by
  simp only [Rect,Fintype.card_prod,Fintype.card_fin,rectCoefficient,pow_two]
  ring

 theorem tagValues_card_pos (K : ℕ) : 0<Fintype.card (I.TagValues K) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨fun _ => 0⟩

 theorem rectangle_code_le (K : ℕ) (v : RawBlock (r:=r) (m:=m) (P:=P) (E:=E) K) :
    rawCode K v≤I.rectCoefficient K*m^2 := by
  apply (rawCode_le K v).trans
  have h := I.tagValues_card_pos K
  unfold rectCoefficient
  gcongr
  exact Nat.le_mul_of_pos_right _ h

 theorem card_bases_le_rectangle (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) :
    Fintype.card (I.Vertex K ε)≤I.rectCoefficient K*m^2 := by
  rw [← Fintype.card_congr (I.rectVertexEquiv K hK hr ε),← I.rect_card K]
  exact Fintype.card_subtype_le _

noncomputable def spacedCount (K : ℕ) (v : I.Block K) : ℕ :=
  rawCode K v.val*(I.rectCoefficient K*m^2+1)

noncomputable def slotLimit (K : ℕ) : ℕ := (I.rectCoefficient K*m^2+1)^2+1

 theorem spacedCount_lt_limit (K : ℕ) (ε : F₂) (v : I.Vertex K ε) :
    I.spacedCount K v.1+1≤I.slotLimit K := by
  have h := I.rectangle_code_le K v.1.val
  unfold spacedCount slotLimit
  nlinarith

noncomputable def slots (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ) :
    (I.Rect K × Fin (I.slotLimit K)) ⊕ Fin q → Option (Marking.Slot (I.Vertex K ε) (fun v => I.spacedCount K v.1)) :=
  Marking.decodeSlots (I.rectVertexEquiv K hK hr ε) (I.slotLimit K) q

 theorem slots_complete (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ)
    (v : Marking.Slot (I.Vertex K ε) (fun v => I.spacedCount K v.1)) :
    ∃!u,I.slots K hK hr ε q u=some v :=
  Marking.decodeSlots_complete (I.rectVertexEquiv K hK hr ε) (I.slotLimit K) q
    (I.spacedCount_lt_limit K ε) v

noncomputable def rectangularGraph (K : ℕ) (hK : 0<K) (hr : 1≤r) (ε : F₂) (q : ℕ) :=
  Marking.rawGraph (I.valuationGraph K ε) (I.slots K hK hr ε q)
end WLTime.Compression.ConsistencyData

namespace WLTime.Pebble
 theorem wins_transport_iff {K : ℕ} {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    (G : SimpleGraph A) (H : SimpleGraph B) (G' : SimpleGraph A') (H' : SimpleGraph B')
    (f : A ≃ A') (g : B ≃ B')
    (hf : ∀x y,G.Adj x y ↔ G'.Adj (f x) (f y))
    (hg : ∀x y,H.Adj x y ↔ H'.Adj (g x) (g y)) :
    Wins G H (fun _ _ => True) (fun _ : Fin K => none) ↔
      Wins G' H' (fun _ _ => True) (fun _ : Fin K => none) := by
  constructor
  · intro h; simpa only [Position.map_none] using h.transport f g hf hg
  · intro h
    have h' := h.transport f.symm g.symm
      (fun x y => by simpa only [Equiv.apply_symm_apply] using (hf (f.symm x) (f.symm y)).symm)
      (fun x y => by simpa only [Equiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm)
    simpa only [Position.map_none] using h'
end WLTime.Pebble

namespace WLTime.Marking
variable {V : Type uV} {W : Type uW} {U : Type uU} [Fintype V] [Fintype W] [Fintype U]
variable (G : SimpleGraph V) (H : SimpleGraph W) (count : V → ℕ) (count' : W → ℕ)
 omit [Fintype V] [Fintype W] in
 theorem raw_wins_iff (a : U → Option (Slot V count)) (b : U → Option (Slot W count'))
    (ha : ∀ v,∃!u,a u=some v) (hb : ∀ v,∃!u,b u=some v)
    (hholes : Fintype.card {u // a u=none}=Fintype.card {u // b u=none}) (K : ℕ) :
    Pebble.Wins (rawGraph G a) (rawGraph H b) (fun _ _ => True) (fun _ : Fin K => none) ↔
      Pebble.Wins (graph G count (Fintype.card {u // a u=none}))
        (graph H count' (Fintype.card {u // a u=none})) (fun _ _ => True) (fun _ : Fin K => none) := by
  classical
  have h := Pebble.wins_transport_iff (K:=K) (rawGraph G a) (rawGraph H b)
    (graph G count _) (graph H count' _) (rawEquiv a ha) (rawEquiv b hb)
    (fun x y => (rawEquiv_adj G a ha x y).symm) (fun x y => (rawEquiv_adj H b hb x y).symm)
  have he := congrArg (fun q => Pebble.Wins (graph G count (Fintype.card {u // a u=none}))
    (graph H count' q) (fun _ _ => True) (fun _ : Fin K => none)) hholes.symm
  exact h.trans (iff_of_eq he)
end WLTime.Marking

namespace WLTime.Compression.ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)
variable [Fintype P] [Fintype E] [Nonempty P]
open scoped Classical

 theorem spaced_wins_iff_ac (hr : 2≤r) (hm : 2 ≤ m) (q : ℕ) :
    Pebble.Wins (Marking.graph (I.valuationGraph (r+2) 0) (fun v => I.spacedCount (r+2) v.1) q)
      (Marking.graph (I.valuationGraph (r+2) 1) (fun v => I.spacedCount (r+2) v.1) q)
      (fun _ _ => True) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  constructor
  · intro h
    apply (I.colored_wins_iff_ac hr).mp
    exact Marking.wins_bases_spaced (I.valuationGraph (r+2) 0) (I.valuationGraph (r+2) 1)
      Sigma.fst Sigma.fst (fun v : I.Block (r+2) => rawCode (r+2) v.val)
      ((rawCode_injective (r+2)).comp Subtype.val_injective)
      (fun v => rawCode_pos (r+2) v.val) (I.baseEquiv (r+2) (by omega)) (fun _ => rfl)
      q (r+2) (I.rectCoefficient (r+2)*m^2) (I.card_bases_le_rectangle (r+2) (by omega) (by omega) 0)
      (I.two_le_card_base (r+2) hm) (by omega) h
  · intro h
    obtain ⟨Q⟩ := I.arcConsistent_iff.mp h
    exact (Marking.liftSystem Sigma.fst Sigma.fst (I.spacedCount (r+2)) q (r+2)
      (I.valuationSystem Q (r+2) (by omega) hr le_rfl)).wins_empty

 theorem rectangular_wins_iff_ac (hr : 2≤r) (hm : 2 ≤ m) (q : ℕ) :
    Pebble.Wins (I.rectangularGraph (r+2) (by omega) (by omega) 0 q)
      (I.rectangularGraph (r+2) (by omega) (by omega) 1 q)
      (fun _ _ => True) (fun _ : Fin (r+2) => none) ↔ I.ArcConsistent := by
  classical
  have hh := Marking.raw_holes_eq (I.baseEquiv (r+2) (by omega)) (fun _ => rfl)
    (I.slots (r+2) (by omega) (by omega) 0 q) (I.slots (r+2) (by omega) (by omega) 1 q)
    (I.slots_complete (r+2) (by omega) (by omega) 0 q) (I.slots_complete (r+2) (by omega) (by omega) 1 q)
  exact (Marking.raw_wins_iff _ _ _ _ _ _
    (I.slots_complete (r+2) (by omega) (by omega) 0 q)
    (I.slots_complete (r+2) (by omega) (by omega) 1 q) hh (r+2)).trans (I.spaced_wins_iff_ac hr hm _)

 omit [Nonempty P] in
 theorem rectangular_card (K q : ℕ) :
    Fintype.card (Option ((I.Rect K × Fin (I.slotLimit K)) ⊕ Fin q))=
      1+I.rectCoefficient K*m^2*((I.rectCoefficient K*m^2+1)^2+1)+q := by
  classical
  rw [Fintype.card_option,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,I.rect_card]
  unfold slotLimit
  omega
end WLTime.Compression.ConsistencyData

end OAI
