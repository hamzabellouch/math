import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialSource

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

abbrev Sites (K N : ℕ) := Fin K × (Fin N × Fin 8)
abbrev Words (K N : ℕ) := Fin K → Fin N → Fin 8 → Fin 7

def sitesEquiv (K N : ℕ) : Sites K N ≃ Fin (8 * K * N) :=
  Fintype.equivOfCardEq (by simp only [Sites, Fintype.card_prod, Fintype.card_fin]; ring)

def flatten (K N : ℕ) (w : Words K N) : AllFieldSource.Word K N :=
  fun i => let p := (sitesEquiv K N).symm i; w p.1 p.2.1 p.2.2

def groupedSource (F : Type*) [Field F] (K N : ℕ) :
    Tensor F (Words K N) (Words K N) (Words K N) :=
  fun x y z => ∏ p : Sites K N,
    FieldCW.tensor F 5 (x p.1 p.2.1 p.2.2) (y p.1 p.2.1 p.2.2) (z p.1 p.2.1 p.2.2)

theorem groupedSource_eq_lots (F : Type*) [Field F] (K N : ℕ) :
    groupedSource F K N =
      familyProduct (fun _ : Fin K => Tensor.power (Tensor.power (FieldCW.tensor F 5) 8) N) := by
  funext x y z
  simp only [groupedSource, Sites, familyProduct, Tensor.power, Fintype.prod_prod_type]

def groupingMap (F : Type*) [Field F] (K N : ℕ) :
    LocalMap (cwSource F K N) (groupedSource F K N) where
  x := fun x s => if s = flatten K N x then 1 else 0
  y := fun y s => if s = flatten K N y then 1 else 0
  z := fun z s => if s = flatten K N z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, cwSource, Tensor.power, groupedSource, flatten]
    apply Fintype.prod_equiv (sitesEquiv K N).symm
    intro i
    rfl

def initialExecution (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (groupedSource F K N) :=
  (startCW F K N).restrict _ (groupingMap F K N)

@[simp] theorem initialExecution_copies (F : Type*) [Field F] (K N : ℕ) :
    Fintype.card (initialExecution F K N).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialSource

end

end OAI
