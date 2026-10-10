import OAI.Computability.WLIdentification.AffinePresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}
namespace Map
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def sumCases {f : ∀ w, A w → C w} {g : ∀ w, B w → C w} (F : Map P R f) (G : Map Q R g) :
    Map (P.sum Q) R (fun w x => x.elim (f w) (g w)) :=
  (Number.sumCases F G).congr (by intro w x; cases x <;> rfl)

def optionCases {f : ∀ w, A w → B w} {g : ∀ w, B w}
    (F : Map P Q f) (h : NatPoly (fun S : Fin 1 → Word => Q.code (S 0) (g (S 0)))) :
    Map P.option Q (fun w x => x.elim (g w) (f w)) :=
  (Number.optionCases F (fun w => Q.code w (g w)) h).congr (by intro w x; cases x <;> rfl)

def const (P : Presented A) (Q : Presented B) (f : ∀ w, B w)
    (h : NatPoly (fun S : Fin 1 → Word => Q.code (S 0) (f (S 0)))) :
    Map P Q (fun w _ => f w) := Number.param P _ h

def boolOfTest {p : ∀ w, A w → Bool} (H : Test P p) : Map P Presented.bool p :=
  (Number.ite H (Number.const P 1) (Number.const P 0)).congr (by intro w x; cases p w x <;> rfl)

end Map
namespace Number
variable {P : Presented A} {Q : Presented B}

def retype {f : ∀ w, A w → ℕ} (F : Number P f) (e : ∀ w, B w ≃ A w) :
    Number (P.retype e) (fun w x => f w (e w x)) := F.comp (Map.retype P e)

noncomputable def fixedOfCode (A : Type) (c : A ↪ ℕ) (b : ℕ) (q : ℕ → Bool)
    (hc : ∀ a,c a<b) (hq : ∀ i,q i=true ↔ ∃a,c a=i) (f : A → ℕ) :
    Number (Presented.ofCode A c b q hc hq) (fun _ x => f x) := by
  classical
  let g : ℕ → ℕ := fun i => if h : ∃a,c a=i then f (Classical.choose h) else 0
  refine ⟨fun _ i => g i, ?_, ?_⟩
  · intro w x
    change g (c x)=f x
    dsimp only [g]
    rw [dite_eq_left ⟨x,rfl⟩]
    congr 1
    exact c.injective (Classical.choose_spec (show ∃a,c a=c x from ⟨x,rfl⟩))
  · apply (NatPoly.fixedTable b g (NatPoly.var 1)).congr
    intro S
    congr 1
    dsimp only
    split_ifs with h
    · rfl
    · dsimp only [g]
      rw [dite_eq_right]
      rintro ⟨a,ha⟩
      exact h (ha ▸ hc a)

end Number
namespace Test
variable {P : Presented A}

def param (P : Presented A) (f : Word → Bool) (h : BoolPoly (fun S : Fin 1 → Word => f (S 0))) :
    Test P (fun w _ => f w) := ⟨fun w _ => f w, fun _ _ => rfl, h.rename (fun _ => 0)⟩

def ofBoolMap {f : ∀ w, A w → Bool} (F : Map P Presented.bool f) : Test P f :=
  (numEq F (Number.const P 1)).congr (by intro w x; cases f w x <;> rfl)

end Test
end FinitePresentation

end WLIdentification

end OAI
