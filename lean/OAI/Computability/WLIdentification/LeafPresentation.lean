import OAI.Computability.WLIdentification.LocalPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A : Word → Type} {P : Presented A} {G : ∀ w, SimpleGraph (A w)}

namespace PresentedGraph
variable (Q : PresentedGraph P G)

theorem adjacent_poly_of {n} {w : (Fin n → Word) → Word} {i j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) (hj : NatPoly j) :
    BoolPoly (fun S => Q.adjacent (w S) (i S) (j S)) := by
  have h := Q.adjacent_poly.subst (g := ![w, fun S => unary (i S), fun S => unary (j S)])
    (by intro k; fin_cases k; exacts [hw,hi,hj])
  simpa [unary] using h

def leafAdj (w : Word) (i j : ℕ) : Bool := if i%2=0 then
  if j%2=0 then Q.adjacent w (i/2) (j/2) else decide (i/2=(Nat.unpair (j/2)).1)
  else if j%2=0 then decide ((Nat.unpair (i/2)).1=j/2) else false

def leaves {ell : ∀ w, A w → ℕ} (E : Number P ell) :
    PresentedGraph (P.sum (P.finSigma E)) (fun w => withLeaves (G w) (ell w)) where
  adjacent := Q.leafAdj
  adjacent_iff w x y := by
    cases x with
    | inl x => cases y with
      | inl y =>
        change Q.leafAdj w (2*P.code w x) (2*P.code w y)=true ↔ (G w).Adj x y
        simpa [leafAdj] using Q.adjacent_iff w x y
      | inr y =>
        change Q.leafAdj w (2*P.code w x) (2*Nat.pair (P.code w y.1) y.2.val+1)=true ↔ x=y.1
        simp [leafAdj, show (2*Nat.pair (P.code w y.1) y.2.val+1)/2=Nat.pair (P.code w y.1) y.2.val by omega,
          (P.code w).injective.eq_iff]
    | inr x => cases y with
      | inl y =>
        change Q.leafAdj w (2*Nat.pair (P.code w x.1) x.2.val+1) (2*P.code w y)=true ↔ x.1=y
        simp [leafAdj, show (2*Nat.pair (P.code w x.1) x.2.val+1)/2=Nat.pair (P.code w x.1) x.2.val by omega,
          (P.code w).injective.eq_iff]
      | inr y =>
        change Q.leafAdj w (2*Nat.pair (P.code w x.1) x.2.val+1) (2*Nat.pair (P.code w y.1) y.2.val+1)=true ↔ False
        simp [leafAdj]
  adjacent_poly := by
    unfold leafAdj
    apply BoolPoly.iteProp (by word_poly)
    · apply BoolPoly.iteProp (by word_poly)
      · apply Q.adjacent_poly_of <;> word_poly
      · word_poly
    · apply BoolPoly.iteProp <;> word_poly

variable [∀ w, Fintype (A w)]

noncomputable def tags {color : ∀ w, A w → ℕ} (F : Number P color) :
    Number P (fun w => tagSize (color w)) :=
  (F.mul (Number.param P (fun w => P.card w+1) (NatPoly.succ P.card_poly))).congr (by
    intro w x
    simp only [tagSize, Presented.card_eq])

noncomputable def tagged {color : ∀ w, A w → ℕ} (F : Number P color) := Q.leaves (tags F)

end PresentedGraph
end FinitePresentation
namespace FinitePresentation
open WordExpressions

theorem rows_get (n m : ℕ) (f : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    (((List.ofFn fun a => List.ofFn (f a)).flatten)[i.val*m+j.val]?).getD false = f i j := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun a => ?_) i
    · rw [List.getElem?_append_left (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp only [List.length_ofFn, Fin.val_succ]; nlinarith)]
      simp only [List.length_ofFn, Fin.val_succ]
      rw [show (a.val+1)*m+j.val-m=a.val*m+j.val by simp only [Nat.add_mul, one_mul]; omega]
      exact ih (fun x => f x.succ) a

namespace PresentedGraph
variable {A : Word → Type} {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

def matrix (w : Word) : Word := (List.range (P.card w * P.card w)).map
  (fun i => Q.adjacent w (P.select w (i/P.card w)) (P.select w (i%P.card w)))

theorem matrix_eq (w : Word) : Q.matrix w=matrixWord (Q.graph w) := by
  apply List.ext_getElem (by simp [matrix, matrixWord_length, graph])
  intro i hi hj
  have hi' : i<P.card w*P.card w := by simpa [matrix] using hi
  have hn : 0<P.card w := by nlinarith
  have hdiv := Nat.div_lt_of_lt_mul hi'
  have hmod := Nat.mod_lt i hn
  have hentry := rows_get (P.card w) (P.card w) (Q.graph w).edge ⟨i/P.card w,hdiv⟩ ⟨i%P.card w,hmod⟩
  rw [show i/P.card w*P.card w+i%P.card w=i by simpa only [Nat.mul_comm] using Nat.div_add_mod i (P.card w)] at hentry
  change (matrixWord (Q.graph w))[i]?.getD false = _ at hentry
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at hentry
  simpa only [matrix, List.getElem_map, List.getElem_range, graph] using hentry.symm

theorem matrix_poly : Poly (fun S : Fin 1 → Word => Q.matrix (S 0)) := by
  apply Poly.tabulateRange (NatPoly.mul P.card_poly P.card_poly)
  apply Q.adjacent_poly_of (Poly.var 0)
  · apply P.select_poly_of (Poly.var 0)
    exact NatPoly.div (NatPoly.var 1) (P.card_poly_of (Poly.var 0))
  · apply P.select_poly_of (Poly.var 0)
    exact NatPoly.mod (NatPoly.var 1) (P.card_poly_of (Poly.var 0))

def output (k : Word → ℕ) (w : Word) : Word :=
  List.replicate (P.card w) true ++ [false] ++ Q.matrix w ++ binaryWord (k w)

theorem output_eq (k : Word → ℕ) (w : Word) : Q.output k w=inputWord (Q.graph w) (binaryWord (k w)) := by
  simp only [output, Q.matrix_eq, inputWord, graph]

theorem output_poly {k : Word → ℕ} (hk : NatPoly (fun S : Fin 1 → Word => k (S 0))) :
    Poly (fun S : Fin 1 → Word => Q.output k (S 0)) :=
  Poly.append (Poly.append (Poly.append (Poly.replicate P.card_poly true) (WordExpressions.Poly.const [false])) Q.matrix_poly)
    (Poly.binary hk)

end PresentedGraph
end FinitePresentation

theorem identifies_isomorphic {G H : Graph} (e : Isomorphic G H) (k : ℕ) : Identifies k G ↔ Identifies k H := by
  constructor
  · intro h I hI
    exact isomorphic_trans (isomorphic_symm e) (h I (equivalent_trans (isomorphic_equivalent e k) hI))
  · intro h I hI
    exact isomorphic_trans e (h I (equivalent_trans (isomorphic_equivalent (isomorphic_symm e) k) hI))

theorem WLdim_isomorphic {G H : Graph} (e : Isomorphic G H) : WLdim G=WLdim H := by
  apply Nat.le_antisymm
  · rw [WLdim_le_iff ((WLdim_spec H).1), identifies_isomorphic e]
    exact (WLdim_le_iff ((WLdim_spec H).1)).mp (le_refl _)
  · rw [WLdim_le_iff ((WLdim_spec G).1), identifies_isomorphic (isomorphic_symm e)]
    exact (WLdim_le_iff ((WLdim_spec G).1)).mp (le_refl _)

end WLIdentification

end OAI
