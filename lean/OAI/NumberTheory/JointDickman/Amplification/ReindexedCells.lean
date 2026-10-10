import OAI.NumberTheory.JointDickman.Probability.PartialWeightedChannel
import OAI.NumberTheory.JointDickman.Amplification.ProductLogCells

namespace OAI

/-! # Reindexing partial output cells -/

namespace JointDickman

open scoped BigOperators

theorem optionCellMass_map_equiv {E A B : Type*} [Fintype E] [DecidableEq A] [DecidableEq B]
    (v : E → ℝ) (cell : E → Option A) (e : A ≃ B) (a : A) :
    optionCellMass v (fun x => (cell x).map e) (e a) = optionCellMass v cell a := by
  unfold optionCellMass
  apply Finset.sum_congr rfl
  intro x _
  cases h : cell x with
  | none => simp [h]
  | some b => simp only [h, Option.map_some, Option.some.injEq, e.injective.eq_iff]

theorem partialFairPrimeTransition_map_equiv {A B : Type*} [DecidableEq A] [DecidableEq B]
    (Q : Finset ℕ) (cell : ℕ → Option A) (e : A ≃ B) (x : Q → Bool) (a : A) :
    partialFairPrimeTransition Q (fun n => (cell n).map e) x (e a) =
      partialFairPrimeTransition Q cell x a :=
  optionCellMass_map_equiv _ _ e a

theorem independentCellMarginal_map_equiv {C E A B : Type*}
    [Fintype C] [Fintype E] [DecidableEq A] [DecidableEq B]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option A) (e : A ≃ B) (a : A) :
    independentCellMarginal w v (fun c x => (cell c x).map e) (e a) =
      independentCellMarginal w v cell a := by
  unfold independentCellMarginal
  simp only [optionCellMass_map_equiv]

def trivialResidueEquiv (A : Type*) : A × (ZMod 1)ˣ ≃ A where
  toFun := Prod.fst
  invFun a := (a, 1)
  left_inv a := by cases a with | mk a r => exact Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

noncomputable def logarithmicCell {A : Type*} [DecidableEq A]
    (B : ℕ) (lower upper : A → ℝ) (n : ℕ) : Option A :=
  (logResidueCell B 1 lower upper n).map (trivialResidueEquiv A)

theorem logarithmicCell_mass {E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (n : E → ℕ) (B : ℕ) (lower upper : A → ℝ) (a : A) :
    optionCellMass v (fun x => logarithmicCell B lower upper (n x)) a =
      optionCellMass v (fun x => logResidueCell B 1 lower upper (n x)) (a, 1) :=
  optionCellMass_map_equiv v _ (trivialResidueEquiv A) (a, 1)

theorem logarithmicCell_primeProduct_mass {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (B : ℕ) (lower upper : A → ℝ)
    (v : (Q → Bool) → ℝ) (c : Q → Bool) (a : A) :
    optionCellMass v (primeProductCell Q (logarithmicCell B lower upper) c) a =
      optionCellMass v (primeProductCell Q (logResidueCell B 1 lower upper) c) (a, 1) :=
  logarithmicCell_mass v _ B lower upper a

theorem logarithmicCell_marginal {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (B : ℕ) (lower upper : A → ℝ) (a : A) :
    independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q (logarithmicCell B lower upper)) a =
      independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q (logResidueCell B 1 lower upper)) (a, 1) :=
  independentCellMarginal_map_equiv _ _ _ (trivialResidueEquiv A) (a, 1)

end JointDickman

end OAI
