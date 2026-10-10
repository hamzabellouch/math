import Mathlib.Data.Fintype.Sigma
import OAI.Algebra.Finitistic.Iteration.BinomialIndex
import OAI.Algebra.Finitistic.Iteration.BinomialBiproduct

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace ExternalTensor.Binomial
universe v u w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
variable {S : Type w} (Phi : C ⥤ C) [Phi.Additive] [Phi.CommShift ℤ]
variable (M : S → C) (H : S → S) (b d : ℤ)

/-- Apply the splitting independently at each object; no naturality in S is present. -/
def branchIteration (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (M Y) ≅
      ⨁ fun x : Branch j => (M ((H^[j]) Y))⟦(j : ℤ)*b + d*(weight x : ℤ)⟧ := by
  induction j with
  | zero =>
    letI : Unique (Branch 0) := inferInstanceAs (Unique Unit)
    simpa only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, mul_zero, zero_add, weight] using
      (shiftZero ℤ (M Y)).symm ≪≫
        (biproductUniqueIso (fun _ : Branch 0 => (M Y)⟦(0 : ℤ)⟧)).symm
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    refine Phi.mapIso ih ≪≫ Phi.mapBiproduct _ ≪≫ ?_
    let X := M ((H^[j+1]) Y)
    let f : Branch j → C := fun x => X⟦((j+1 : ℕ) : ℤ)*b + d*(weight x : ℤ)⟧
    let g : Branch j → C := fun x => X⟦((j+1 : ℕ) : ℤ)*b + d*((weight x+1 : ℕ) : ℤ)⟧
    have step (x : Branch j) :
        Phi.obj ((M ((H^[j]) Y))⟦(j : ℤ)*b+d*(weight x : ℤ)⟧) ≅ f x ⊞ g x := by
      simpa only [f, g, X, Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one,
        add_mul, mul_add, mul_one, one_mul, add_assoc, add_left_comm, add_comm] using
        splitShift Phi (M ((H^[j]) Y)) (M (H ((H^[j]) Y))) b d
          ((j : ℤ)*b+d*(weight x : ℤ)) (split ((H^[j]) Y))
    refine biproduct.mapIso step ≪≫ biproductBiprod f g ≪≫ biproduct.mapIso (J := Branch j ⊕ Branch j)
      (f := Sum.elim f g)
      (g := fun x : Branch j ⊕ Branch j =>
        (M ((H^[j+1]) Y))⟦((j+1 : ℕ) : ℤ)*b + d*(weight (n := j+1) x : ℤ)⟧) ?_
    intro x
    cases x with
    | inl x => exact Iso.refl _
    | inr x => exact Iso.refl _

/-- The manuscript's repeated finite biproduct, including the multiplicity index. -/
def binomialObject (j : ℕ) (X : C) : C :=
  ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
    X⟦(j : ℤ)*b + d*(q.val : ℤ)⟧

/-- Regroup by weight using the proved fiber cardinality, not an assumed decomposition. -/
def groupBiproduct (j : ℕ) (X : C) :
    (⨁ fun x : Branch j => X⟦(j : ℤ)*b + d*(weight x : ℤ)⟧) ≅
      binomialObject b d j X :=
  biproduct.whiskerEquiv
    (f := fun x : Branch j => X⟦(j : ℤ)*b + d*(weight x : ℤ)⟧)
    (g := fun p : Σ q : Fin (j+1), Fin (Nat.choose j q.val) =>
      X⟦(j : ℤ)*b + d*(p.1.val : ℤ)⟧)
    (groupEquiv j) (fun _ => Iso.refl _) ≪≫
    (biproductBiproductIso (fun q : Fin (j+1) => Fin (Nat.choose j q.val))
      (fun q _ => X⟦(j : ℤ)*b + d*(q.val : ℤ)⟧)).symm

/-- Categorical binomial iteration with a common shift offset. -/
def binomialIteration (split : ∀ Y, Phi.obj (M Y) ≅ (M (H Y))⟦b⟧ ⊞ (M (H Y))⟦b+d⟧)
    (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (M Y) ≅ binomialObject b d j (M ((H^[j]) Y)) :=
  branchIteration Phi M H b d split j Y ≪≫ groupBiproduct b d j _

/-- Section 4, final corollary, with only objectwise splitting isomorphisms. -/
def section4Iteration (split : ∀ Y, Phi.obj (M Y) ≅ M (H Y) ⊞ (M (H Y))⟦(3 : ℤ)⟧)
    (j : ℕ) (Y : S) :
    (Phi.obj^[j]) (M Y) ≅
      ⨁ fun q : Fin (j+1) => ⨁ fun _ : Fin (Nat.choose j q.val) =>
        (M ((H^[j]) Y))⟦(3 : ℤ)*(q.val : ℤ)⟧ := by
  have h (Y : S) : Phi.obj (M Y) ≅ (M (H Y))⟦(0 : ℤ)⟧ ⊞ (M (H Y))⟦(0+3 : ℤ)⟧ :=
    split Y ≪≫ biprod.mapIso (shiftZero ℤ (M (H Y))).symm (Iso.refl _)
  simpa only [binomialObject, mul_zero, zero_add] using binomialIteration Phi M H 0 3 h j Y
end ExternalTensor.Binomial

end

end OAI
