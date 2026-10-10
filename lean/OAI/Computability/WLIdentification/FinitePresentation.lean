import OAI.Computability.WLIdentification.DimensionDecider

namespace OAI

namespace WLIdentification
/- Polynomially presented finite types. Membership refers to actual natural
codes and all iteration bounds have literal unary word realizers. -/
namespace FinitePresentation
open WordExpressions

structure Presented (A : Word → Type) where
  code : (w : Word) → A w ↪ ℕ
  bound : Word → ℕ
  good : Word → ℕ → Bool
  code_lt : ∀ w x, code w x < bound w
  good_iff : ∀ w i, good w i = true ↔ ∃ x, code w x = i
  bound_poly : NatPoly (fun S : Fin 1 → Word => bound (S 0))
  good_poly : BoolPoly (fun S : Fin 2 → Word => good (S 0) (S 1).length)

namespace Presented
variable {A B : Word → Type}

@[simp] theorem good_code (P : Presented A) (w : Word) (x : A w) : P.good w (P.code w x)=true :=
  (P.good_iff w _).mpr ⟨x,rfl⟩

theorem good_lt (P : Presented A) {w : Word} {i : ℕ} (h : P.good w i=true) : i<P.bound w := by
  obtain ⟨x,rfl⟩ := (P.good_iff w i).mp h
  exact P.code_lt w x

theorem bound_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} (hw : WordExpressions.Poly w) :
    NatPoly (fun S => P.bound (w S)) := by
  exact P.bound_poly.subst (g := fun _ => w) (fun _ => hw)

theorem good_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : WordExpressions.Poly w) (hi : NatPoly i) : BoolPoly (fun S => P.good (w S) (i S)) := by
  have h := P.good_poly.subst (g := ![w, fun S => unary (i S)]) (by intro i; fin_cases i; exacts [hw,hi])
  simpa [unary] using h

noncomputable def fixed (A : Type) [Fintype A] : Presented (fun _ => A) where
  code _ := NaturalCode.fixed A
  bound _ := Fintype.card A
  good _ i := decide (i<Fintype.card A)
  code_lt _ x := (Fintype.equivFin A x).isLt
  good_iff w i := by
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨(Fintype.equivFin A).symm ⟨i,h⟩, congrArg Fin.val ((Fintype.equivFin A).apply_symm_apply _)⟩
    · rintro ⟨x,rfl⟩; exact (Fintype.equivFin A x).isLt
  bound_poly := NatPoly.const _
  good_poly := NatPoly.lt (NatPoly.var _) (NatPoly.const _)

def fin (f : Word → ℕ) (hf : NatPoly (fun S : Fin 1 → Word => f (S 0))) :
    Presented (fun w => Fin (f w)) where
  code w := NaturalCode.fin (f w)
  bound := f
  good w i := decide (i<f w)
  code_lt _ x := x.isLt
  good_iff w i := by simp only [decide_eq_true_eq]; exact ⟨fun h => ⟨⟨i,h⟩,rfl⟩, fun ⟨x,h⟩ => h ▸ x.isLt⟩
  bound_poly := hf
  good_poly := NatPoly.lt (NatPoly.var _) (hf.rename (fun _ => 0))

def subtype (P : Presented A) (p : (w : Word) → A w → Prop) (q : Word → ℕ → Bool)
    (hq : ∀ w x, q w (P.code w x)=true ↔ p w x)
    (hp : BoolPoly (fun S : Fin 2 → Word => q (S 0) (S 1).length)) :
    Presented (fun w => {x : A w // p w x}) where
  code w := NaturalCode.subtype (P.code w) (p w)
  bound := P.bound
  good w i := P.good w i && q w i
  code_lt w x := P.code_lt w x.val
  good_iff w i := by
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h,hq'⟩
      obtain ⟨x,rfl⟩ := (P.good_iff w i).mp h
      exact ⟨⟨x,(hq w x).mp hq'⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨P.good_code w x.val,(hq w x.val).mpr x.property⟩
  bound_poly := P.bound_poly
  good_poly := BoolPoly.and P.good_poly hp

def sigma (P : Presented A) (B : (w : Word) → A w → Type)
    (c : ∀ w x, B w x ↪ ℕ) (b : Word → ℕ) (q : Word → ℕ → ℕ → Bool)
    (hc : ∀ w x y, c w x y < b w)
    (hq : ∀ w x i, q w (P.code w x) i=true ↔ ∃ y, c w x y=i)
    (hb : NatPoly (fun S : Fin 1 → Word => b (S 0)))
    (hp : BoolPoly (fun S : Fin 3 → Word => q (S 0) (S 1).length (S 2).length)) :
    Presented (fun w => Σ x, B w x) where
  code w := NaturalCode.sigma (P.code w) (c w)
  bound w := Nat.pair (P.bound w) (b w)+1
  good w i := P.good w (Nat.unpair i).1 && q w (Nat.unpair i).1 (Nat.unpair i).2
  code_lt w x := by
    exact (Nat.pair_lt_pair_left _ (P.code_lt w x.1)).trans
      ((Nat.pair_lt_pair_right _ (hc w x.1 x.2)).trans_le (Nat.le_succ _))
  good_iff w i := by
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨h,hq'⟩
      obtain ⟨x,hx⟩ := (P.good_iff w _).mp h
      rw [← hx] at hq'
      obtain ⟨y,hy⟩ := (hq w x _).mp hq'
      exact ⟨⟨x,y⟩, by change Nat.pair _ _ = i; rw [hx,hy,Nat.pair_unpair]⟩
    · rintro ⟨⟨x,y⟩,rfl⟩
      change P.good w (Nat.unpair (Nat.pair _ _)).1=true ∧ q w (Nat.unpair (Nat.pair _ _)).1 (Nat.unpair (Nat.pair _ _)).2=true
      rw [Nat.unpair_pair]
      exact ⟨P.good_code w x,(hq w x _).mpr ⟨y,rfl⟩⟩
  bound_poly := NatPoly.succ (NatPoly.pair P.bound_poly hb)
  good_poly := by
    apply BoolPoly.and
    · apply P.good_poly_of <;> word_poly
    · have h := hp.subst (g := ![fun S : Fin 2 → Word => S 0,
        fun S => unary (Nat.unpair (S 1).length).1, fun S => unary (Nat.unpair (S 1).length).2])
        (by intro i; fin_cases i <;> word_poly)
      simpa [unary] using h

end Presented
end FinitePresentation

namespace FinitePresentation.Presented
open WordExpressions
variable {A B : Word → Type}

def retype (P : Presented A) (e : ∀ w, B w ≃ A w) : Presented B where
  code w := (e w).toEmbedding.trans (P.code w)
  bound := P.bound
  good := P.good
  code_lt w x := P.code_lt w (e w x)
  good_iff w i := (P.good_iff w i).trans ⟨fun ⟨x,h⟩ => ⟨(e w).symm x, by simpa using h⟩,
    fun ⟨x,h⟩ => ⟨e w x,h⟩⟩
  bound_poly := P.bound_poly
  good_poly := P.good_poly

def prod (P : Presented A) (Q : Presented B) : Presented (fun w => A w × B w) :=
  (P.sigma (fun w _ => B w) (fun w _ => Q.code w) Q.bound (fun w _ => Q.good w)
    (fun w _ y => Q.code_lt w y) (fun w _ i => Q.good_iff w i) Q.bound_poly
    (Q.good_poly.rename ![0,2])).retype (fun _ => Equiv.sigmaEquivProd _ _ |>.symm)

def sum (P : Presented A) (Q : Presented B) : Presented (fun w => A w ⊕ B w) where
  code w := NaturalCode.sum (P.code w) (Q.code w)
  bound w := 2*(P.bound w+Q.bound w)+2
  good w i := if i%2=0 then P.good w (i/2) else Q.good w (i/2)
  code_lt w x := by cases x with
    | inl a => have := P.code_lt w a; change 2*P.code w a < _; omega
    | inr b => have := Q.code_lt w b; change 2*Q.code w b+1 < _; omega
  good_iff w i := by
    by_cases he : i%2=0
    · simp only [he, ↓reduceIte, P.good_iff]
      constructor
      · rintro ⟨a,ha⟩
        refine ⟨.inl a, ?_⟩
        change 2*P.code w a=i
        omega
      · rintro ⟨a,ha⟩
        cases a with
        | inl a => exact ⟨a, by change 2*P.code w a=i at ha; omega⟩
        | inr b => change 2*Q.code w b+1=i at ha; omega
    · simp only [he, ↓reduceIte, Q.good_iff]
      constructor
      · rintro ⟨b,hb⟩
        refine ⟨.inr b, ?_⟩
        change 2*Q.code w b+1=i
        omega
      · rintro ⟨a,ha⟩
        cases a with
        | inl a => change 2*P.code w a=i at ha; omega
        | inr b => exact ⟨b, by change 2*Q.code w b+1=i at ha; omega⟩
  bound_poly := by word_poly; exact P.bound_poly; exact Q.bound_poly
  good_poly := by
    apply BoolPoly.iteProp
    · word_poly
    · apply P.good_poly_of <;> word_poly
    · apply Q.good_poly_of <;> word_poly

def option (P : Presented A) : Presented (fun w => Option (A w)) where
  code w := NaturalCode.option (P.code w)
  bound w := P.bound w+1
  good w i := decide (i=0) || (decide (0 < i) && P.good w (i-1))
  code_lt w x := by cases x with
    | none => change 0 < P.bound w+1; omega
    | some a => exact Nat.succ_lt_succ (P.code_lt w a)
  good_iff w i := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨hi,hg⟩)
      · exact ⟨none,rfl⟩
      · obtain ⟨a,ha⟩ := (P.good_iff w _).mp hg
        exact ⟨some a, by change P.code w a+1=i; omega⟩
    · rintro ⟨x,rfl⟩
      cases x with
      | none => exact Or.inl rfl
      | some a => exact Or.inr ⟨by change 0 < P.code w a+1; omega, by change P.good w (P.code w a+1-1)=true; simp⟩
  bound_poly := NatPoly.succ P.bound_poly
  good_poly := BoolPoly.or (NatPoly.eqtest (NatPoly.var _) (NatPoly.const _))
    (BoolPoly.and (NatPoly.lt (NatPoly.const 0) (NatPoly.var _))
      (P.good_poly_of (Poly.var _) (NatPoly.sub (NatPoly.var _) (NatPoly.const 1))))

def bool : Presented (fun _ => Bool) where
  code _ := NaturalCode.bool
  bound _ := 2
  good _ i := decide (i<2)
  code_lt _ x := by cases x <;> decide
  good_iff _ i := by
    simp only [decide_eq_true_eq]
    constructor
    · intro hi
      interval_cases i
      · exact ⟨false,rfl⟩
      · exact ⟨true,rfl⟩
    · rintro ⟨x,rfl⟩; cases x <;> decide
  bound_poly := NatPoly.const _
  good_poly := NatPoly.lt (NatPoly.var _) (NatPoly.const 2)

def unit : Presented (fun _ => Unit) where
  code _ := NaturalCode.unit
  bound _ := 1
  good _ i := decide (i=0)
  code_lt _ x := by cases x; decide
  good_iff _ i := by simp only [decide_eq_true_eq]; exact ⟨fun h => ⟨(),h.symm⟩,fun ⟨_,h⟩ => h.symm⟩
  bound_poly := NatPoly.const _
  good_poly := NatPoly.eqtest (NatPoly.var _) (NatPoly.const 0)

end FinitePresentation.Presented

namespace FinitePresentation.Presented
open WordExpressions NumericFinite
variable {A : Word → Type}

abbrev card (P : Presented A) (w : Word) := count (P.bound w) (P.good w)
abbrev select (P : Presented A) (w : Word) (i : ℕ) := NumericFinite.select (P.bound w) (P.good w) i

theorem rank_lt (P : Presented A) (w : Word) (x : A w) : count (P.code w x) (P.good w) < P.card w :=
  count_strict (P.code_lt w x) (P.good_code w x)

theorem select_good (P : Presented A) (w : Word) {i : ℕ} (hi : i<P.card w) :
    P.good w (P.select w i)=true := by
  rw [select, select_correct _ _ _ hi]
  exact (mem_elements.mp (List.getElem_mem hi)).2

theorem rank_select (P : Presented A) (w : Word) {i : ℕ} (hi : i<P.card w) :
    count (P.select w i) (P.good w)=i := by
  rw [select, select_correct _ _ _ hi]
  exact NumericFinite.rank _ _ _ hi

theorem select_rank (P : Presented A) (w : Word) (x : A w) :
    P.select w (count (P.code w x) (P.good w))=P.code w x := by
  have hr := P.rank_select w (P.rank_lt w x)
  have hg := P.select_good w (P.rank_lt w x)
  rcases lt_trichotomy (P.select w (count (P.code w x) (P.good w))) (P.code w x) with hl | he | hl
  · have := count_strict hl hg; omega
  · exact he
  · have := count_strict hl (P.good_code w x); omega

noncomputable def decode (P : Presented A) (w : Word) (i : Fin (P.card w)) : A w :=
  Classical.choose ((P.good_iff w _).mp (P.select_good w i.isLt))

theorem code_decode (P : Presented A) (w : Word) (i : Fin (P.card w)) :
    P.code w (P.decode w i)=P.select w i :=
  Classical.choose_spec ((P.good_iff w _).mp (P.select_good w i.isLt))

noncomputable def rankEquiv (P : Presented A) (w : Word) : A w ≃ Fin (P.card w) where
  toFun x := ⟨count (P.code w x) (P.good w), P.rank_lt w x⟩
  invFun := P.decode w
  left_inv x := by apply (P.code w).injective; rw [P.code_decode, P.select_rank]
  right_inv i := by apply Fin.ext; exact (congrArg (fun j => count j (P.good w)) (P.code_decode w i)).trans (P.rank_select w i.isLt)

@[simp] theorem card_eq (P : Presented A) (w : Word) [Fintype (A w)] : P.card w=Fintype.card (A w) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (P.rankEquiv w)).symm

theorem card_poly (P : Presented A) : NatPoly (fun S : Fin 1 → Word => P.card (S 0)) := by
  apply (NatPoly.filterCount P.bound_poly P.good_poly).congr
  intro S
  simp [Fin.snoc, unary, card]

theorem card_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} (hw : Poly w) :
    NatPoly (fun S => P.card (w S)) :=
  P.card_poly.subst (g := fun _ => w) (fun _ => hw)

theorem select_poly (P : Presented A) : NatPoly (fun S : Fin 2 → Word => P.select (S 0) (S 1).length) := by
  apply (NatPoly.filterSelect (P.bound_poly.rename (fun _ => 0)) (NatPoly.var 1)
    (P.good_poly.rename ![0,2])).congr
  intro S
  simp [Fin.snoc, unary, select]

theorem select_poly_of (P : Presented A) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => P.select (w S) (i S)) := by
  have h := P.select_poly.subst (g := ![w, fun S => unary (i S)]) (by intro i; fin_cases i; exacts [hw,hi])
  simpa [unary] using h

end FinitePresentation.Presented

namespace FinitePresentation
open WordExpressions
variable {A : Word → Type}

structure PresentedGraph (P : Presented A) (G : ∀ w, SimpleGraph (A w)) where
  adjacent : Word → ℕ → ℕ → Bool
  adjacent_iff : ∀ w x y, adjacent w (P.code w x) (P.code w y)=true ↔ (G w).Adj x y
  adjacent_poly : BoolPoly (fun S : Fin 3 → Word => adjacent (S 0) (S 1).length (S 2).length)

namespace PresentedGraph
variable {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

noncomputable def graph (w : Word) : Graph where
  order := P.card w
  edge i j := Q.adjacent w (P.select w i) (P.select w j)
  symmetric i j := by
    rw [← P.code_decode w i, ← P.code_decode w j]
    apply Bool.eq_iff_iff.mpr
    rw [Q.adjacent_iff, Q.adjacent_iff, (G w).adj_comm]
  loopless i := by
    rw [← P.code_decode w i]
    apply Bool.eq_false_iff.mpr
    intro h
    exact (G w).loopless.irrefl _ ((Q.adjacent_iff w _ _).mp h)

theorem graph_isomorphic (w : Word) [Fintype (A w)] : Isomorphic (Q.graph w) (graphOfSimple (G w)) := by
  classical
  refine ⟨(P.rankEquiv w).symm.trans (Fintype.equivFin (A w)), ?_⟩
  intro i j
  change Q.adjacent w (P.select w i) (P.select w j) = _
  rw [← P.code_decode w i, ← P.code_decode w j]
  change _ = (graphOfSimple (G w)).edge (Fintype.equivFin _ (P.decode w i)) (Fintype.equivFin _ (P.decode w j))
  rw [graphOfSimple_edge]
  apply Bool.eq_iff_iff.mpr
  simp only [Q.adjacent_iff, decide_eq_true_eq]

end PresentedGraph
end FinitePresentation

end WLIdentification

end OAI
