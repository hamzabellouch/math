import OAI.Computability.WLIdentification.FinitePresentation

namespace OAI

namespace WLIdentification

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

structure Number (P : Presented A) (f : ∀ w, A w → ℕ) where
  eval : Word → ℕ → ℕ
  correct : ∀ w x, eval w (P.code w x)=f w x
  poly : NatPoly (fun S : Fin 2 → Word => eval (S 0) (S 1).length)

structure Test (P : Presented A) (f : ∀ w, A w → Bool) where
  eval : Word → ℕ → Bool
  correct : ∀ w x, eval w (P.code w x)=f w x
  poly : BoolPoly (fun S : Fin 2 → Word => eval (S 0) (S 1).length)

abbrev Map (P : Presented A) (Q : Presented B) (f : ∀ w, A w → B w) :=
  Number P (fun w x => Q.code w (f w x))

namespace Number
variable {P : Presented A} {f g : ∀ w, A w → ℕ}

theorem eval_poly (F : Number P f) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => F.eval (w S) (i S)) := by
  have h := F.poly.subst (g := ![w,fun S => unary (i S)]) (by intro j; fin_cases j; exacts [hw,hi])
  simpa [unary] using h

def congr (F : Number P f) (h : ∀ w x, f w x=g w x) : Number P g :=
  { F with correct := fun w x => (F.correct w x).trans (h w x) }

def code (P : Presented A) : Number P (fun w x => P.code w x) :=
  ⟨fun _ i => i, fun _ _ => rfl, NatPoly.var 1⟩

def param (P : Presented A) (f : Word → ℕ) (h : NatPoly (fun S : Fin 1 → Word => f (S 0))) :
    Number P (fun w _ => f w) :=
  ⟨fun w _ => f w, fun _ _ => rfl, h.rename (fun _ => 0)⟩

def const (P : Presented A) (k : ℕ) : Number P (fun _ _ => k) := param P (fun _ => k) (NatPoly.const k)

def add (F : Number P f) (G : Number P g) : Number P (fun w x => f w x+g w x) :=
  ⟨fun w i => F.eval w i+G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.add F.poly G.poly⟩
def mul (F : Number P f) (G : Number P g) : Number P (fun w x => f w x*g w x) :=
  ⟨fun w i => F.eval w i*G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.mul F.poly G.poly⟩
def sub (F : Number P f) (G : Number P g) : Number P (fun w x => f w x-g w x) :=
  ⟨fun w i => F.eval w i-G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.sub F.poly G.poly⟩
def pair (F : Number P f) (G : Number P g) : Number P (fun w x => Nat.pair (f w x) (g w x)) :=
  ⟨fun w i => Nat.pair (F.eval w i) (G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.pair F.poly G.poly⟩
def mod (F : Number P f) (G : Number P g) : Number P (fun w x => f w x%g w x) :=
  ⟨fun w i => F.eval w i%G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.mod F.poly G.poly⟩
def div (F : Number P f) (G : Number P g) : Number P (fun w x => f w x/g w x) :=
  ⟨fun w i => F.eval w i/G.eval w i, fun w x => by rw [F.correct,G.correct], NatPoly.div F.poly G.poly⟩

def comp {Q : Presented B} {h : ∀ w, A w → B w} {f : ∀ w, B w → ℕ}
    (F : Number Q f) (H : Map P Q h) : Number P (fun w x => f w (h w x)) where
  eval w i := F.eval w (H.eval w i)
  correct w x := by rw [H.correct,F.correct]
  poly := F.eval_poly (Poly.var 0) H.poly

end Number
namespace Test
variable {P : Presented A} {f g : ∀ w, A w → Bool}

theorem eval_poly (F : Test P f) {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : BoolPoly (fun S => F.eval (w S) (i S)) := by
  have h := F.poly.subst (g := ![w,fun S => unary (i S)]) (by intro j; fin_cases j; exacts [hw,hi])
  simpa [unary] using h

def congr (F : Test P f) (h : ∀ w x, f w x=g w x) : Test P g :=
  { F with correct := fun w x => (F.correct w x).trans (h w x) }

def const (P : Presented A) (b : Bool) : Test P (fun _ _ => b) :=
  ⟨fun _ _ => b,fun _ _ => rfl,BoolPoly.const b⟩

def and (F : Test P f) (G : Test P g) : Test P (fun w x => f w x && g w x) :=
  ⟨fun w i => F.eval w i && G.eval w i, fun w x => by rw [F.correct,G.correct], BoolPoly.and F.poly G.poly⟩
def or (F : Test P f) (G : Test P g) : Test P (fun w x => f w x || g w x) :=
  ⟨fun w i => F.eval w i || G.eval w i, fun w x => by rw [F.correct,G.correct], BoolPoly.or F.poly G.poly⟩
def not (F : Test P f) : Test P (fun w x => !(f w x)) :=
  ⟨fun w i => !(F.eval w i), fun w x => by rw [F.correct], BoolPoly.not F.poly⟩

def numEq {f g : ∀ w, A w → ℕ} (F : Number P f) (G : Number P g) : Test P (fun w x => decide (f w x=g w x)) :=
  ⟨fun w i => decide (F.eval w i=G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.eqtest F.poly G.poly⟩
def numLt {f g : ∀ w, A w → ℕ} (F : Number P f) (G : Number P g) : Test P (fun w x => decide (f w x<g w x)) :=
  ⟨fun w i => decide (F.eval w i<G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.lt F.poly G.poly⟩

def comp {Q : Presented B} {h : ∀ w, A w → B w} {f : ∀ w, B w → Bool}
    (F : Test Q f) (H : Map P Q h) : Test P (fun w x => f w (h w x)) where
  eval w i := F.eval w (H.eval w i)
  correct w x := by rw [H.correct,F.correct]
  poly := F.eval_poly (Poly.var 0) H.poly

end Test
namespace Number
variable {P : Presented A}

def ite {p : ∀ w, A w → Bool} {f g : ∀ w, A w → ℕ}
    (H : Test P p) (F : Number P f) (G : Number P g) : Number P (fun w x => if p w x then f w x else g w x) where
  eval w i := if H.eval w i then F.eval w i else G.eval w i
  correct w x := by rw [H.correct,F.correct,G.correct]
  poly := NatPoly.ite H.poly F.poly G.poly

end Number
namespace Map

def id (P : Presented A) : Map P P (fun _ x => x) := Number.code P

def fst (P : Presented A) (Q : Presented B) : Map (P.prod Q) P (fun _ x => x.1) where
  eval _ i := (Nat.unpair i).1
  correct w x := by change (Nat.unpair (Nat.pair _ _)).1 = _; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_fst (NatPoly.var _)

def snd (P : Presented A) (Q : Presented B) : Map (P.prod Q) Q (fun _ x => x.2) where
  eval _ i := (Nat.unpair i).2
  correct w x := by change (Nat.unpair (Nat.pair _ _)).2 = _; rw [Nat.unpair_pair]; rfl
  poly := NatPoly.unpair_snd (NatPoly.var _)

def pair {P : Presented A} {Q : Presented B} {R : Presented C}
    {f : ∀ w, A w → B w} {g : ∀ w, A w → C w} (F : Map P Q f) (G : Map P R g) :
    Map P (Q.prod R) (fun w x => (f w x,g w x)) := Number.pair F G

end Map
end FinitePresentation

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

namespace Number
variable {P : Presented A} {Q : Presented B}

def sumCases {f : ∀ w, A w → ℕ} {g : ∀ w, B w → ℕ} (F : Number P f) (G : Number Q g) :
    Number (P.sum Q) (fun w x => x.elim (f w) (g w)) where
  eval w i := if i%2=0 then F.eval w (i/2) else G.eval w (i/2)
  correct w x := by
    cases x with
    | inl a => change (if (2*P.code w a)%2=0 then F.eval w ((2*P.code w a)/2) else G.eval w ((2*P.code w a)/2))=_; simp [F.correct]
    | inr b => change (if (2*Q.code w b+1)%2=0 then F.eval w ((2*Q.code w b+1)/2) else G.eval w ((2*Q.code w b+1)/2))=_; simp [show (2*Q.code w b+1)/2=Q.code w b by omega, G.correct]
  poly := NatPoly.iteProp (by word_poly)
    (F.eval_poly (Poly.var _) (by word_poly)) (G.eval_poly (Poly.var _) (by word_poly))

def optionCases {f : ∀ w, A w → ℕ} (F : Number P f) (g : Word → ℕ)
    (hg : NatPoly (fun S : Fin 1 → Word => g (S 0))) :
    Number P.option (fun w x => x.elim (g w) (f w)) where
  eval w i := if i=0 then g w else F.eval w (i-1)
  correct w x := by cases x with
    | none => rfl
    | some a => change (if P.code w a+1=0 then g w else F.eval w (P.code w a+1-1))=_; simp [F.correct]
  poly := NatPoly.iteProp (by word_poly) (hg.rename (fun _ => 0))
    (F.eval_poly (Poly.var _) (by word_poly))

def envelope {f : ∀ w, A w → ℕ} (F : Number P f) (w : Word) : ℕ :=
  ((List.range (P.bound w)).map (F.eval w)).sum+1

theorem lt_envelope {f : ∀ w, A w → ℕ} (F : Number P f) (w : Word) (x : A w) :
    f w x < F.envelope w := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨P.code w x, List.mem_range.mpr (P.code_lt w x), F.correct w x⟩)
  exact Nat.lt_succ_of_le h

theorem envelope_poly {f : ∀ w, A w → ℕ} (F : Number P f) :
    NatPoly (fun S : Fin 1 → Word => F.envelope (S 0)) := by
  exact NatPoly.succ (NatPoly.sumRange P.bound_poly (by simpa using F.poly))

end Number
namespace Presented

def finSigma (P : Presented A) {f : ∀ w, A w → ℕ} (F : Number P f) :
    Presented (fun w => Σ x : A w, Fin (f w x)) :=
  P.sigma (fun w x => Fin (f w x)) (fun _ _ => NaturalCode.fin _) F.envelope
    (fun w i j => decide (j<F.eval w i))
    (fun w x y => y.isLt.trans (F.lt_envelope w x))
    (by intro w x i; rw [F.correct, decide_eq_true_eq]; exact ⟨fun h => ⟨⟨i,h⟩,rfl⟩,fun ⟨j,h⟩ => h ▸ j.isLt⟩)
    F.envelope_poly (NatPoly.lt (NatPoly.var 2) (F.eval_poly (Poly.var 0) (NatPoly.var 1)))

def restrict (P : Presented A) (p : ∀ w, A w → Prop) [∀ w x, Decidable (p w x)]
    (H : Test P (fun w x => decide (p w x))) : Presented (fun w => {x : A w // p w x}) :=
  P.subtype p H.eval (by intro w x; rw [H.correct, decide_eq_true_eq]) H.poly

end Presented
namespace Map
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def comp {f : ∀ w, A w → B w} {g : ∀ w, B w → C w} (G : Map Q R g) (F : Map P Q f) :
    Map P R (fun w x => g w (f w x)) := Number.comp (P := P) (Q := Q) (h := f) (f := fun w y => R.code w (g w y)) G F

def inl (P : Presented A) (Q : Presented B) : Map P (P.sum Q) (fun _ x => Sum.inl x) :=
  (Number.const P 2).mul (Number.code P)

def inr (P : Presented A) (Q : Presented B) : Map Q (P.sum Q) (fun _ x => Sum.inr x) :=
  ((Number.const Q 2).mul (Number.code Q)).add (Number.const Q 1)

def none (P : Presented A) (Q : Presented B) : Map P Q.option (fun _ _ => none) := Number.const P 0

def some (P : Presented A) : Map P P.option (fun _ x => some x) := (Number.code P).add (Number.const P 1)

def retype (P : Presented A) (e : ∀ w, B w ≃ A w) : Map (P.retype e) P (fun w x => e w x) :=
  Number.code (P.retype e)

def untype (P : Presented A) (e : ∀ w, B w ≃ A w) : Map P (P.retype e) (fun w x => (e w).symm x) :=
  (Number.code P).congr (by intro w x; change P.code w x=P.code w (e w ((e w).symm x)); rw [Equiv.apply_symm_apply])

def sigmaFst (P : Presented A) {f : ∀ w, A w → ℕ} (F : Number P f) :
    Map (P.finSigma F) P (fun _ x => x.1) where
  eval _ i := (Nat.unpair i).1
  correct w x := by change (Nat.unpair (Nat.pair _ _)).1=_; rw [Nat.unpair_pair]
  poly := NatPoly.unpair_fst (NatPoly.var _)

def coe (P : Presented A) (p : ∀ w, A w → Prop) [∀ w x, Decidable (p w x)]
    (H : Test P (fun w x => decide (p w x))) : Map (P.restrict p H) P (fun _ x => x.val) :=
  Number.code (P.restrict p H)

end Map
namespace Test
variable {P : Presented A} {Q : Presented B}

def ite {p f g : ∀ w, A w → Bool} (H : Test P p) (F : Test P f) (G : Test P g) :
    Test P (fun w x => if p w x then f w x else g w x) where
  eval w i := if H.eval w i then F.eval w i else G.eval w i
  correct w x := by rw [H.correct,F.correct,G.correct]
  poly := BoolPoly.ite H.poly F.poly G.poly

def sumCases {f : ∀ w, A w → Bool} {g : ∀ w, B w → Bool} (F : Test P f) (G : Test Q g) :
    Test (P.sum Q) (fun w x => x.elim (f w) (g w)) where
  eval w i := if i%2=0 then F.eval w (i/2) else G.eval w (i/2)
  correct w x := by
    cases x with
    | inl a => change (if (2*P.code w a)%2=0 then F.eval w ((2*P.code w a)/2) else G.eval w ((2*P.code w a)/2))=_; simp [F.correct]
    | inr b => change (if (2*Q.code w b+1)%2=0 then F.eval w ((2*Q.code w b+1)/2) else G.eval w ((2*Q.code w b+1)/2))=_; simp [show (2*Q.code w b+1)/2=Q.code w b by omega, G.correct]
  poly := BoolPoly.iteProp (by word_poly)
    (F.eval_poly (Poly.var _) (by word_poly)) (G.eval_poly (Poly.var _) (by word_poly))

def optionCases {f : ∀ w, A w → Bool} (F : Test P f) (g : Word → Bool)
    (hg : BoolPoly (fun S : Fin 1 → Word => g (S 0))) :
    Test P.option (fun w x => x.elim (g w) (f w)) where
  eval w i := if i=0 then g w else F.eval w (i-1)
  correct w x := by cases x with
    | none => rfl
    | some a => change (if P.code w a+1=0 then g w else F.eval w (P.code w a+1-1))=_; simp [F.correct]
  poly := BoolPoly.iteProp (by word_poly) (hg.rename (fun _ => 0))
    (F.eval_poly (Poly.var _) (by word_poly))

def eq [∀ w, DecidableEq (B w)] {f g : ∀ w, A w → B w} (F : Map P Q f) (G : Map P Q g) :
    Test P (fun w x => decide (f w x=g w x)) :=
  (numEq F G).congr (by intro w x; simp only [(Q.code w).injective.eq_iff])

end Test
end FinitePresentation

namespace WordExpressions.NatPoly
variable {n : ℕ}

theorem fixedTable (b : ℕ) (f : ℕ → ℕ) {i : (Fin n → Word) → ℕ} (hi : NatPoly i) :
    NatPoly (fun S => if i S<b then f (i S) else 0) := by
  induction b with
  | zero => simpa using const (n := n) 0
  | succ b ih =>
    apply (iteProp (eqtest hi (const b)) (const (f b)) ih).congr
    intro S
    by_cases h : i S=b
    · simp [h]
    · by_cases h' : i S<b
      · simp [h,h',show i S<b+1 by omega]
      · simp [h,h',show ¬i S<b+1 by omega]

end WordExpressions.NatPoly
namespace WordExpressions.BoolPoly
variable {n : ℕ}

theorem fixedTable (b : ℕ) (f : ℕ → Bool) {i : (Fin n → Word) → ℕ} (hi : NatPoly i) :
    BoolPoly (fun S => if i S<b then f (i S) else false) := by
  apply (Poly.nth (Poly.const ((List.range b).map f)) hi).congr
  intro S
  by_cases h : i S<b
  · simp [h]
  · simp [h]

end WordExpressions.BoolPoly
namespace FinitePresentation
open WordExpressions

noncomputable def Presented.ofCode (A : Type) (code : A ↪ ℕ) (bound : ℕ)
    (good : ℕ → Bool) (hcode : ∀ a, code a<bound)
    (hgood : ∀ i, good i=true ↔ ∃ a, code a=i) : Presented (fun _ => A) where
  code _ := code
  bound _ := bound
  good _ := good
  code_lt _ := hcode
  good_iff _ := hgood
  bound_poly := NatPoly.const _
  good_poly := by
    apply (BoolPoly.fixedTable bound good (NatPoly.var 1)).congr
    intro S
    congr 1
    dsimp only
    split_ifs with h
    · rfl
    · apply Eq.symm
      apply Bool.eq_false_iff.mpr
      intro hg
      obtain ⟨a,ha⟩ := (hgood _).mp hg
      exact h (ha ▸ hcode a)

noncomputable def Number.fixed (A : Type) [Fintype A] (f : A → ℕ) :
    Number (Presented.fixed A) (fun _ x => f x) where
  eval _ i := if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else 0
  correct w x := by
    change (if h : (Fintype.equivFin A x).val<Fintype.card A then f ((Fintype.equivFin A).symm ⟨(Fintype.equivFin A x).val,h⟩) else _)=_
    simp
  poly := by
    apply (NatPoly.fixedTable (Fintype.card A)
      (fun i => if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else 0)
      (NatPoly.var 1)).congr
    intro S
    dsimp only
    split_ifs <;> simp_all

noncomputable def Test.fixed (A : Type) [Fintype A] (f : A → Bool) :
    Test (Presented.fixed A) (fun _ x => f x) where
  eval _ i := if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else false
  correct w x := by
    change (if h : (Fintype.equivFin A x).val<Fintype.card A then f ((Fintype.equivFin A).symm ⟨(Fintype.equivFin A x).val,h⟩) else _)=_
    simp
  poly := by
    apply (BoolPoly.fixedTable (Fintype.card A)
      (fun i => if h : i<Fintype.card A then f ((Fintype.equivFin A).symm ⟨i,h⟩) else false)
      (NatPoly.var 1)).congr
    intro S
    congr 1
    dsimp only
    split_ifs <;> simp_all

end FinitePresentation

end WLIdentification

end OAI
