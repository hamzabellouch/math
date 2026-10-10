import OAI.Computability.WeisfeilerLeman.Tableau

namespace OAI

universe uA uJ uK uAlphabet

namespace WLTime.CircuitEncoding.Tableau
variable {A : Type uA} {J : Type uJ} {K : Type uK} (F : A → A → A → A) (s : Equiv.Perm J) (t : Equiv.Perm K)
  (e : J ≃ K) (u : J → A) (v : K → A)

theorem run_reindex (hstep : ∀ j,e (s j)=t (e j)) (hinit : ∀ j,u j=v (e j))
    (n : ℕ) (j : J) : run F s u n j=run F t v n (e j) := by
  have hinv (j : J) : e (s.symm j)=t.symm (e j) := by
    apply t.injective
    rw [t.apply_symm_apply,← hstep,s.apply_symm_apply]
  induction n generalizing j with
  | zero => exact hinit j
  | succ n ih => simp only [run_succ,ih,hinv,hstep]
end WLTime.CircuitEncoding.Tableau

namespace WLTime.Digits

theorem value_lt_base_iff {q m : ℕ} (hm : 0< m) (a : Word (q+1) m) :
    value a< m ↔ ∀ i : Fin q,(a i.succ).val=0 := by
  rw [← value_eq_zero_iff hm (fun i => a i.succ),value_succ]
  have hhead := (a 0).isLt
  constructor
  · intro h
    by_contra hh
    have hx : 1 ≤ value (fun i => a i.succ) := Nat.one_le_iff_ne_zero.mpr hh
    have hh' := Nat.mul_le_mul_left m hx
    omega
  · intro h
    simp only [h,Nat.mul_zero,Nat.add_zero]
    exact hhead

 theorem finEquiv_val {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n j).val=j.val := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => rfl

 theorem finEquiv_shift {n : ℕ} [NeZero n] (j : Fin n) :
    ZMod.finEquiv n (inc n j)=OneTape.ringShift n (ZMod.finEquiv n j) := by
  apply ZMod.val_injective
  rw [finEquiv_val,inc_value]
  change (if j.val+1=n then 0 else j.val+1)=((ZMod.finEquiv n j)+1).val
  have h1 : (1 : ZMod n).val=1%n := by simpa only [Nat.cast_one] using ZMod.val_natCast n 1
  rw [ZMod.val_add,finEquiv_val,h1]
  by_cases hn : n=1
  · subst n
    simp
  · have hn' : 1<n := by have := NeZero.ne n; omega
    rw [Nat.mod_eq_of_lt hn']
    by_cases hj : j.val+1=n
    · simp [hj]
    · rw [ite_eq_right hj,Nat.mod_eq_of_lt (by have := j.isLt; omega)]

end WLTime.Digits

namespace WLTime.OneTape
variable (M : OneTape)
open CircuitEncoding

 def blankCell : M.Cell := (⟨0,by have := M.symbols_ge; omega⟩,none)

 def inputCell (w : List Bool) (i : Fin w.length) : M.Cell :=
  (M.toTM.symbol (w.getD i.val false),
    if i.val=0 then some ⟨0,by have := M.states_ge; omega⟩ else none)

 theorem ring_initial_digits (w : List Bool) (hm : 0< w.length) (q : ℕ)
    [NeZero (w.length^(q+1))] (j : Fin (w.length^(q+1))) :
    BoxTableau.initialRing (M.inputCell w) M.blankCell j=
      M.snapshot (M.ringInitial (w.length^(q+1)) w) (ZMod.finEquiv (w.length^(q+1)) j) := by
  have hval : Digits.value (Digits.encode.symm j)=j.val := by
    simp only [Digits.value,Equiv.apply_symm_apply]
  have hzero : ZMod.finEquiv (w.length^(q+1)) j=0 ↔ j.val=0 := by
    rw [← ZMod.val_eq_zero,Digits.finEquiv_val]
  unfold BoxTableau.initialRing BoxTableau.initialDigit
  by_cases hj : j.val< w.length
  · have ht := (Digits.value_lt_base_iff hm (Digits.encode.symm j)).mp (hval ▸ hj)
    rw [ite_eq_left ht]
    have ha : ((Digits.encode.symm j) 0).val=j.val := by
      have hz := (Digits.value_eq_zero_iff hm (fun i => Digits.encode.symm j i.succ)).mpr ht
      rw [Digits.value_succ,hz,Nat.mul_zero,Nat.add_zero] at hval
      exact hval
    simp [inputCell,snapshot,ringInitial,Digits.finEquiv_val,ha,hj,hzero]
  · have ht : ¬∀ i : Fin q,(Digits.encode.symm j i.succ).val=0 := by
      rw [← Digits.value_lt_base_iff hm,hval]
      exact hj
    rw [ite_eq_right ht]
    have hz : j.val≠0 := by omega
    simp [blankCell,snapshot,ringInitial,Digits.finEquiv_val,hj,hzero,hz]

theorem product_simulation (w : List Bool) (hm : 0< w.length) (d q T : ℕ)
    (hT : T ≤ w.length^d-1) (hL : 2*T+w.length+2< w.length^(q+1))
    (hh : (M.run lineShift (M.initial w) T).state.val=1 ∨
      (M.run lineShift (M.initial w) T).state.val=2) :
    (∀ g, (BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting :
      Schematic (d+(q+1)) w.length _ _ _ _).expand.test g=true →
      ¬(BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting).expand.TrueAt g) ↔
      ¬M.toTM.accepts w := by
  let : NeZero (w.length^(q+1)) := ⟨Nat.ne_of_gt (Nat.pow_pos hm)⟩
  rw [BoxTableau.local_equivalence M.localRule (M.inputCell w) M.blankCell M.letterAccepting hm]
  rw [← M.ring_accepts_iff w T (w.length^(q+1)) (w.length^d-1) hL hT hh]
  simp only [not_exists]
  constructor
  · intro h j
    let f : Fin (w.length^(q+1)) ≃ ZMod (w.length^(q+1)) := (ZMod.finEquiv _).toEquiv
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) f
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) (f.symm j)
    exact (by simpa only [f.apply_symm_apply] using he) ▸ h (f.symm j)
  · intro h j
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) (ZMod.finEquiv _).toEquiv
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) j
    rw [he]
    exact h _

end WLTime.OneTape

namespace WLTime.CircuitEncoding.BoxTableau
open NatCode ProductBox
namespace Formula
variable {Alphabet : Type uAlphabet} {J : Type uJ} {d q m : ℕ}

def labelDomain (e : Label Alphabet d q) (M a : Expr J) : Fin (d+q) → Predicate J :=
  match e with
  | .left _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun i => ProductBox.Formula.carryDomain s i M a)
  | .center _ _ _ t => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun _ => .truth true)
  | .bridge _ _ _ => fun _ => .truth true
  | .right _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryDomain t.castSucc i M a)
      (fun i => ProductBox.Formula.borrowDomain s i M a)
  | .out _ _ _ => fun _ => .truth true

def labelCoord (e : Label Alphabet d q) (M a : Expr J) : Fin (d+q) → Expr J :=
  match e with
  | .left _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a)
      (fun i => ProductBox.Formula.carryCoord s i M a)
  | .center _ _ _ t => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a) (fun _ => a)
  | .bridge _ _ _ => fun _ => a
  | .right _ _ _ t s => Fin.addCases (fun i => ProductBox.Formula.carryCoord t.castSucc i M a)
      (fun i => ProductBox.Formula.borrowCoord s i M a)
  | .out _ _ _ => fun _ => a

 theorem labelDomain_correct (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (labelDomain e M a i).Holds σ w ↔ x∈(box e).domain i := by
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelDomain,box,Box.product,Fin.addCases_right] using ProductBox.Formula.carryDomain_correct s i M a σ w x hM ha
  | center f g h t =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simp only [labelDomain,Fin.addCases_right,box,Box.product,Box.identity,Predicate.Holds,Finset.mem_univ]
  | bridge f g h => simp only [labelDomain,box,Box.identity,Predicate.Holds,Finset.mem_univ]
  | right f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelDomain,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryDomain_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelDomain,box,Box.product,Fin.addCases_right] using ProductBox.Formula.borrowDomain_correct s i M a σ w x hM ha
  | out f g h => simp only [labelDomain,box,Box.identity,Predicate.Holds,Finset.mem_univ]

 theorem labelCoord_correct (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (labelCoord e M a i).eval σ w=((box e).coord i x).val := by
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Fin.addCases_right] using ProductBox.Formula.carryCoord_correct s i M a σ w x hM ha
  | center f g h t =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Box.identity,Fin.addCases_right,Equiv.refl_apply] using ha
  | bridge f g h => exact ha
  | right f g h t s =>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [labelCoord,box,Box.product,Fin.addCases_left] using ProductBox.Formula.carryCoord_correct t.castSucc i M a σ w x hM ha
    · simpa only [labelCoord,box,Box.product,Fin.addCases_right] using ProductBox.Formula.borrowCoord_correct s i M a σ w x hM ha
  | out f g h => exact ha

noncomputable def position (input : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) : Fin (q+1) → Predicate J :=
  match s with
  | .inl f => Fin.cases (input f a) (fun _ => .eq a (.const 0))
  | .inr i => fun j => if j=i.succ then (Predicate.eq a (.const 0)).neg else .truth true

noncomputable def seed (input : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) : Fin (d+(q+1)) → Predicate J :=
  Fin.addCases (fun _ => .eq a (.const 0)) (position input s a)

def test (M a : Expr J) : Fin (d+(q+1)) → Predicate J :=
  Fin.addCases (fun _ => .eq (.binary .add a (.const 1)) M) (fun _ => .truth true)

 theorem position_correct [DecidableEq Alphabet] (input : Fin m → Alphabet)
    (C : Alphabet → Expr J → Predicate J) (σ : J → ℕ) (w : List Bool)
    (hC : ∀f a (x : Fin m),a.eval σ w=x.val → ((C f a).Holds σ w ↔ input x=f))
    (s : Alphabet ⊕ Fin q) (a : Expr J) (i : Fin (q+1)) (x : Fin m) (ha : a.eval σ w=x.val) :
    (position C s a i).Holds σ w ↔ x∈positionDomain input s i := by
  cases s with
  | inl f =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [position,positionDomain,Fin.cases_zero,Finset.mem_filter,Finset.mem_univ,true_and]
        using hC f a x ha
    · simp only [position,positionDomain,Fin.cases_succ,Predicate.Holds,Expr.eval,ha,
        Finset.mem_filter,Finset.mem_univ,true_and]
  | inr j =>
    simp only [position,positionDomain,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs <;> simp_all only [Predicate.Holds,Expr.eval,true_implies,false_implies]

 theorem seed_correct [DecidableEq Alphabet] (input : Fin m → Alphabet)
    (C : Alphabet → Expr J → Predicate J) (σ : J → ℕ) (w : List Bool)
    (hC : ∀f a (x : Fin m),a.eval σ w=x.val → ((C f a).Holds σ w ↔ input x=f))
    (s : Alphabet ⊕ Fin q) (a : Expr J) (i : Fin (d+(q+1))) (x : Fin m) (ha : a.eval σ w=x.val) :
    (seed C s a i).Holds σ w ↔ x∈seedDomain input s i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [seed,seedDomain,Fin.addCases_left,Predicate.Holds,Expr.eval,ha,
      Finset.mem_filter,Finset.mem_univ,true_and]
  · simpa only [seed,seedDomain,Fin.addCases_right] using position_correct input C σ w hC s a i x ha

 theorem test_correct (accepting : Alphabet → Prop) (f : {f // accepting f})
    (M a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool)
    (x : Fin m) (hM : M.eval σ w=m) (ha : a.eval σ w=x.val) :
    (test M a i).Holds σ w ↔ x∈testDomain accepting f i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [test,testDomain,Fin.addCases_left,Predicate.Holds,Expr.eval,Binary.eval,hM,ha,
      Finset.mem_filter,Finset.mem_univ,true_and]
  · simp only [test,testDomain,Fin.addCases_right,Predicate.Holds,Finset.mem_univ]
end Formula
end WLTime.CircuitEncoding.BoxTableau

namespace WLTime.OneTape
open NatCode
variable (M : OneTape) {J : Type uJ}
noncomputable def inputPredicate (f : M.Cell) (a : Expr J) : Predicate J := by
  classical
  exact (((Predicate.bit a).conj (.truth (decide (M.toTM.symbol true=f.1)))).disj
    ((Predicate.bit a).neg.conj (.truth (decide (M.toTM.symbol false=f.1))))).conj
      (((Predicate.eq a (.const 0)).conj (.truth (decide (some (⟨0,by have := M.states_ge; omega⟩ : Fin M.states)=f.2)))).disj
        ((Predicate.eq a (.const 0)).neg.conj (.truth (decide ((none : Option (Fin M.states))=f.2)))))

 theorem inputPredicate_correct (f : M.Cell) (a : Expr J) (σ : J → ℕ) (w : List Bool)
    (x : Fin w.length) (ha : a.eval σ w=x.val) :
    (M.inputPredicate f a).Holds σ w ↔ M.inputCell w x=f := by
  classical
  simp only [inputPredicate,Predicate.holds_disj,Predicate.Holds,Expr.eval,ha,
    decide_eq_true_eq,inputCell,Prod.ext_iff]
  cases w.getD x.val false <;> by_cases hx : x.val=0 <;> simp [hx] <;> tauto
end WLTime.OneTape

namespace WLTime.NatCode
variable {J : Type uJ}
namespace Predicate
 theorem bounded_mono (p : Predicate J) (σ : J → ℕ) (w : List Bool) {A B : ℕ}
    (h : p.Bounded σ w A) (hAB : A≤B) : p.Bounded σ w B := by
  induction p with
  | truth => trivial
  | eq a b | lt a b => exact ⟨a.bounded_mono σ w h.1 hAB,b.bounded_mono σ w h.2 hAB⟩
  | bit a => exact a.bounded_mono σ w h hAB
  | conj a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | neg a ha => exact ha h

@[simp] theorem bounded_disj (p q : Predicate J) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (p.disj q).Bounded σ w B ↔ p.Bounded σ w B ∧ q.Bounded σ w B := Iff.rfl

@[simp] theorem bounded_all (l : List (Predicate J)) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (all l).Bounded σ w B ↔ ∀p∈l,p.Bounded σ w B := by
  induction l with
  | nil => simp only [all,List.foldr_nil,Bounded,List.not_mem_nil,false_implies,implies_true]
  | cons p l ih =>
    change p.Bounded σ w B ∧ (all l).Bounded σ w B ↔ _
    simp only [ih,List.mem_cons,forall_eq_or_imp]

@[simp] theorem bounded_any (l : List (Predicate J)) (σ : J → ℕ) (w : List Bool) (B : ℕ) :
    (any l).Bounded σ w B ↔ ∀p∈l,p.Bounded σ w B := by
  simp only [any,Bounded,bounded_all,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
end Predicate
namespace Expr
 theorem addOne_bounded (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) : (binary .add a (.const 1)).Bounded σ w (B+1) :=
  ⟨a.bounded_mono σ w ha (by omega),by change 1≤B+1; omega,by
    change a.eval σ w+1≤B+1
    exact Nat.add_le_add_right (a.eval_le σ w B ha) 1⟩

 theorem subOne_bounded (a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (ha : a.Bounded σ w B) : (binary .sub a (.const 1)).Bounded σ w B :=
  ⟨ha,hB,by change a.eval σ w-1≤B; exact (Nat.sub_le _ _).trans (a.eval_le σ w B ha)⟩

 theorem incCode_bounded (M a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (incCode M a).Bounded σ w (5*B) := by
  have ht := addOne_bounded a σ w B ha
  have h := choose_bounded (.eq (.binary .add a (.const 1)) M) (.const 0)
    (.binary .add a (.const 1)) σ w (B+1) ⟨ht,M.bounded_mono σ w hM (by omega)⟩ (by exact Nat.zero_le _) ht
  exact (incCode M a).bounded_mono σ w h (by omega)

 theorem decCode_bounded (M a : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (decCode M a).Bounded σ w (3*B) := by
  have h := choose_bounded (.eq a (.const 0)) (.binary .sub M (.const 1))
    (.binary .sub a (.const 1)) σ w B ⟨ha,Nat.zero_le _⟩ (subOne_bounded M σ w B hB hM)
      (subOne_bounded a σ w B hB ha)
  exact (decCode M a).bounded_mono σ w h (by omega)
end Expr
end WLTime.NatCode

namespace WLTime.ProductBox.Formula
open NatCode
variable {d : ℕ} {J : Type uJ}
 theorem carryDomain_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (carryDomain p i M a).Bounded σ w (2*B) := by
  have ht := (Expr.binary .add a (.const 1)).bounded_mono σ w (Expr.addOne_bounded a σ w B ha) (by omega : B+1≤2*B)
  have hm := M.bounded_mono σ w hM (by omega : B≤2*B)
  unfold carryDomain
  split_ifs <;> first | exact ⟨ht,hm⟩ | trivial

 theorem carryCoord_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (carryCoord p i M a).Bounded σ w (5*B) := by
  unfold carryCoord
  split_ifs
  · exact Expr.incCode_bounded M a σ w B hB hM ha
  · exact a.bounded_mono σ w ha (by omega)

 theorem borrowCoord_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (borrowCoord p i M a).Bounded σ w (3*B) := by
  unfold borrowCoord
  split_ifs
  · exact Expr.decCode_bounded M a σ w B hB hM ha
  · exact a.bounded_mono σ w ha (by omega)

 theorem borrowDomain_bounded (p : Fin (d+1)) (i : Fin d) (M a : Expr J)
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (borrowDomain p i M a).Bounded σ w (6*B) := by
  have h := carryDomain_bounded p i M (borrowCoord p i M a) σ w (3*B) (by omega)
    (M.bounded_mono σ w hM (by omega)) (borrowCoord_bounded p i M a σ w B hB hM ha)
  simpa only [borrowDomain,← Nat.mul_assoc] using h
end WLTime.ProductBox.Formula
namespace WLTime.CircuitEncoding.BoxTableau.Formula
open NatCode
variable {Alphabet : Type uAlphabet} {d q : ℕ} {J : Type uJ}
 theorem labelDomain_bounded (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (labelDomain e M a i).Bounded σ w (6*B) := by
  have hcarry {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.carryDomain p j M a).bounded_mono σ w
      (ProductBox.Formula.carryDomain_bounded p j M a σ w B hB hM ha) (by omega : 2*B≤6*B)
  have hborrow {n} (p : Fin (n+1)) (j : Fin n) :=
    ProductBox.Formula.borrowDomain_bounded p j M a σ w B hB hM ha
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelDomain,Fin.addCases_right] using hcarry s j
  | center f g h t =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simp only [labelDomain,Fin.addCases_right,Predicate.Bounded]
  | bridge | out => trivial
  | right f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelDomain,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelDomain,Fin.addCases_right] using hborrow s j

 theorem labelCoord_bounded (e : Label Alphabet d q) (M a : Expr J) (i : Fin (d+q))
    (σ : J → ℕ) (w : List Bool) (B : ℕ) (hB : 1≤B)
    (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (labelCoord e M a i).Bounded σ w (6*B) := by
  have hcarry {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.carryCoord p j M a).bounded_mono σ w
      (ProductBox.Formula.carryCoord_bounded p j M a σ w B hB hM ha) (by omega : 5*B≤6*B)
  have hborrow {n} (p : Fin (n+1)) (j : Fin n) :=
    (ProductBox.Formula.borrowCoord p j M a).bounded_mono σ w
      (ProductBox.Formula.borrowCoord_bounded p j M a σ w B hB hM ha) (by omega : 3*B≤6*B)
  have hid := a.bounded_mono σ w ha (by omega : B≤6*B)
  cases e with
  | left f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hcarry s j
  | center f g h t =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hid
  | bridge | out => exact hid
  | right f g h t s =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [labelCoord,Fin.addCases_left] using hcarry t.castSucc j
    · simpa only [labelCoord,Fin.addCases_right] using hborrow s j

 theorem position_bounded (C : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) (i : Fin (q+1)) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hC : ∀f,(C f a).Bounded σ w B) :
    (position C s a i).Bounded σ w B := by
  cases s with
  | inl f =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [position,Fin.cases_zero] using hC f
    · simpa only [position,Fin.cases_succ,Predicate.Bounded,Expr.Bounded,and_true] using
        (show a.Bounded σ w B ∧ 0≤B from ⟨ha,Nat.zero_le _⟩)
  | inr j =>
    simp only [position]
    split_ifs
    · exact ⟨ha,Nat.zero_le _⟩
    · trivial

 theorem seed_bounded (C : Alphabet → Expr J → Predicate J) (s : Alphabet ⊕ Fin q)
    (a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool) (B : ℕ)
    (ha : a.Bounded σ w B) (hC : ∀f,(C f a).Bounded σ w B) :
    (seed C s a i).Bounded σ w B := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [seed,Fin.addCases_left,Predicate.Bounded,Expr.Bounded] using
      (show a.Bounded σ w B ∧ 0≤B from ⟨ha,Nat.zero_le _⟩)
  · simpa only [seed,Fin.addCases_right] using position_bounded C s a j σ w B ha hC

 theorem test_bounded (M a : Expr J) (i : Fin (d+(q+1))) (σ : J → ℕ) (w : List Bool)
    (B : ℕ) (hB : 1≤B) (hM : M.Bounded σ w B) (ha : a.Bounded σ w B) :
    (test (d:=d) (q:=q) M a i).Bounded σ w (2*B) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [test,Fin.addCases_left,Predicate.Bounded]
    exact ⟨(Expr.binary .add a (.const 1)).bounded_mono σ w (Expr.addOne_bounded a σ w B ha) (by omega),
      M.bounded_mono σ w hM (by omega)⟩
  · simp only [test,Fin.addCases_right,Predicate.Bounded]
end WLTime.CircuitEncoding.BoxTableau.Formula

end OAI
