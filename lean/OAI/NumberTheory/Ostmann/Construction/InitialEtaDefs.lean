import OAI.NumberTheory.Ostmann.Construction.HalfListBounds
import OAI.NumberTheory.Ostmann.Construction.SelectedCellSources

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

abbrev HalfPosition (b s : ℕ) (ι : Type*) := Unit ⊕ (Fin b ⊕ (Fin s ⊕ ι))
abbrev Position (b s : ℕ) (ι : Type*) := Bool × HalfPosition b s ι
abbrev JointSample (giant bulk spectator : PrimeSource) {ι : Type*}
    (aux : ι → PrimeSource) (b s : ℕ) :=
  HalfListSample giant bulk spectator aux b s × HalfListSample giant bulk spectator aux b s

def halfAt {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (h : Bool) :
    HalfListSample giant bulk spectator aux b s := if h then x.2 else x.1

def halfSource (giant bulk spectator : PrimeSource) {ι : Type*}
    (aux : ι → PrimeSource) (b s : ℕ) : HalfPosition b s ι → PrimeSource
  | .inl _ => giant
  | .inr (.inl _) => bulk
  | .inr (.inr (.inl _)) => spectator
  | .inr (.inr (.inr i)) => aux i

def tupleSource (giant bulk spectator : PrimeSource) {ι : Type*}
    (aux : ι → PrimeSource) (b s : ℕ) (i : Position b s ι) : PrimeSource :=
  halfSource giant bulk spectator aux b s i.2

def halfSample {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : HalfListSample giant bulk spectator aux b s) :
    (i : HalfPosition b s ι) → (halfSource giant bulk spectator aux b s i).Sample
  | .inl _ => x.1
  | .inr (.inl i) => x.2.1 i
  | .inr (.inr (.inl i)) => x.2.2.1 i
  | .inr (.inr (.inr i)) => x.2.2.2 i

def tupleSample {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (i : Position b s ι) :
    (tupleSource giant bulk spectator aux b s i).Sample := halfSample (halfAt x i.1) i.2

def tupleValues {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (i : Position b s ι) : ℕ :=
  (tupleSample x i : ℕ)

def jointPrior (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ) :
    FinitePrior (JointSample giant bulk spectator aux b s) :=
  (halfListPrior giant bulk spectator aux b s).pair (halfListPrior giant bulk spectator aux b s)

def tupleEquiv (giant bulk spectator : PrimeSource) {ι : Type*}
    (aux : ι → PrimeSource) (b s : ℕ) :
    JointSample giant bulk spectator aux b s ≃
      ((i : Position b s ι) → (tupleSource giant bulk spectator aux b s i).Sample) where
  toFun := tupleSample
  invFun z :=
    ((z (false,.inl ()),(fun i => z (false,.inr (.inl i))),
      (fun i => z (false,.inr (.inr (.inl i)))),(fun i => z (false,.inr (.inr (.inr i))))),
     (z (true,.inl ()),(fun i => z (true,.inr (.inl i))),
      (fun i => z (true,.inr (.inr (.inl i)))),(fun i => z (true,.inr (.inr (.inr i))))))
  left_inv x := rfl
  right_inv z := by
    funext i
    rcases i with ⟨h,i⟩
    cases h <;> rcases i with ⟨⟨⟩⟩ | (i | (i | i)) <;> rfl

theorem tupleValues_prime {giant bulk spectator : PrimeSource} {ι : Type*}
    {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (i : Position b s ι) :
    Nat.Prime (tupleValues x i) :=
  (tupleSource giant bulk spectator aux b s i).prime _ (tupleSample x i).property

@[simp] theorem card_position (b s : ℕ) (ι : Type*) [Fintype ι] :
    Fintype.card (Position b s ι) = 2+2*b+2*s+2*Fintype.card ι := by
  simp only [Position,HalfPosition,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum,
    Fintype.card_unique,Fintype.card_fin]
  omega

def tuplePhysical (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (X : ℝ)
    (x : JointSample giant bulk spectator aux b s) : ℂ :=
  (∑' n : ℤ, SchwartzCutoff.psi ((n:ℝ)/X) *
    ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.1 : ℝ) : ℂ) *
    ((halfListTupleTest d P giant bulk spectator aux b s tb td n x.2 : ℝ) : ℂ)) /
      (Real.sqrt X : ℂ)

def repeatedContribution (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ)
    (tb td : ℤ) (X : ℝ) : ℂ := by
  classical
  exact (jointPrior giant bulk spectator aux b s).cmean (fun x =>
    if Function.Injective (tupleValues x) then 0
    else tuplePhysical d P giant bulk spectator aux b s tb td X x)

def distinctContribution (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ)
    (tb td : ℤ) (X : ℝ) : ℂ := by
  classical
  exact (jointPrior giant bulk spectator aux b s).cmean (fun x =>
    if Function.Injective (tupleValues x) then
      tuplePhysical d P giant bulk spectator aux b s tb td X x else 0)

end Ostmann.Construction.InitialEta

end

end OAI
