import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCChildProducts

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

abbrev ChildWords := (Fin 1 → Fin 7) × (Fin 1 → Fin 7)

def singletonChildWords (p : ChildPair) : ChildWords :=
  (fun _ => p.1, fun _ => p.2)

def collapseChildWords (w : ChildWords) : ChildPair := (w.1 0, w.2 0)

@[simp] theorem singleton_collapse_childWords (w : ChildWords) :
    singletonChildWords (collapseChildWords w) = w := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

def placedShapeChildProduct (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) : Tensor F ChildWords ChildWords ChildWords :=
  Tensor.product
    (CWStrands.shapeTensor (Fin 1) (fun i => branchAtom s b (phi.symm i)))
    (CWStrands.shapeTensor (Fin 1)
      (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i)))

theorem placedShapeChildProduct_eq_stageC (F : Type*) [CommRing F]
    (u : AllFieldParameters.Shape) (hu : u ∈ AllFieldParameters.shapes 4)
    (hpos : AllFieldParameters.positive u = true)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    placedShapeChildProduct F (AllFieldHistory.stageCDistinguished u) phi b =
      Tensor.product
        (CWStrands.shapeTensor (Fin 1) (fun i => AllFieldHistory.stageCAtom u b (phi.symm i)))
        (CWStrands.shapeTensor (Fin 1) (fun i => u (phi.symm i) -
          AllFieldHistory.stageCAtom u b (phi.symm i))) := by
  unfold placedShapeChildProduct
  rw [branchAtom_eq_stageCAtom, shape_eq_parent u hu hpos]

theorem placedShapeChildProduct_pullback (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    Tensor.pullback singletonChildWords singletonChildWords singletonChildWords
      (placedShapeChildProduct F s phi b) = placedChildProduct F s phi b := by
  rw [placedChildProduct_eq]
  funext x y z
  have hL := congrFun (congrFun (congrFun
    (siteTensor_eq_shapeTensor F (fun i => branchAtom s b (phi.symm i))) x.1) y.1) z.1
  have hR := congrFun (congrFun (congrFun
    (siteTensor_eq_shapeTensor F
      (fun i => shape s (phi.symm i) - branchAtom s b (phi.symm i))) x.2) y.2) z.2
  exact congrArg₂ (fun a b : F => a * b) hL hR

theorem placedShapeChildProduct_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (b : Fin 4) :
    ∃ (a : (Row (phi s) b × Middle (phi s) b) → ChildWords → F)
      (c : (Middle (phi s) b × Column (phi s) b) → ChildWords → F)
      (e : (Column (phi s) b × Row (phi s) b) → ChildWords → F),
      Tensor.restrict a c e (placedShapeChildProduct F s phi b) =
        Tensor.matrixCoefficients (Row (phi s) b) (Middle (phi s) b) (Column (phi s) b) := by
  classical
  let E : ChildPair → ChildWords → F := fun p w => if w = singletonChildWords p then 1 else 0
  have hE : Tensor.restrict E E E (placedShapeChildProduct F s phi b) =
      placedChildProduct F s phi b := by
    rw [← Tensor.pullback_eq_restrict]
    exact placedShapeChildProduct_pullback F s phi b
  obtain ⟨a, c, e, h⟩ := placedChildProduct_restriction F s phi b
  refine ⟨Tensor.composeRestrictionMatrix a E, Tensor.composeRestrictionMatrix c E,
    Tensor.composeRestrictionMatrix e E, ?_⟩
  rw [← Tensor.restrict_restrict, hE, h]

def placedShapeChildProducts (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    Tensor F (Positions counts → ChildWords) (Positions counts → ChildWords)
      (Positions counts → ChildWords) :=
  CommonDimensions.familyProduct
    (fun p : Positions counts => placedShapeChildProduct F s phi p.1)

theorem placedShapeChildProducts_collapse (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ)
    (x y z : Positions counts → ChildWords) :
    placedChildProducts F s phi counts (collapseChildWords ∘ x)
      (collapseChildWords ∘ y) (collapseChildWords ∘ z) =
      placedShapeChildProducts F s phi counts x y z := by
  dsimp only [placedChildProducts, placedShapeChildProducts, CommonDimensions.familyProduct]
  apply Finset.prod_congr rfl
  intro p _
  have h := congrFun (congrFun (congrFun (placedShapeChildProduct_pullback F s phi p.1)
    (collapseChildWords (x p))) (collapseChildWords (y p))) (collapseChildWords (z p))
  simpa only [Tensor.pullback, singleton_collapse_childWords, Function.comp_apply] using h.symm

theorem placedShapeChildProducts_restriction (F : Type*) [CommRing F] (s : Fin 3)
    (phi : Equiv.Perm (Fin 3)) (counts : Fin 4 → ℕ) :
    ∃ (a : (RowWords (phi s) counts × MiddleWords (phi s) counts) →
        (Positions counts → ChildWords) → F)
      (c : (MiddleWords (phi s) counts × ColumnWords (phi s) counts) →
        (Positions counts → ChildWords) → F)
      (e : (ColumnWords (phi s) counts × RowWords (phi s) counts) →
        (Positions counts → ChildWords) → F),
      Tensor.restrict a c e (placedShapeChildProducts F s phi counts) =
        Tensor.matrixCoefficients (RowWords (phi s) counts) (MiddleWords (phi s) counts)
          (ColumnWords (phi s) counts) := by
  classical
  choose a c e h using fun p : Positions counts => placedShapeChildProduct_restriction F s phi p.1
  exact TerminalProducts.matrix_restriction_of_history_restrictions
    (fun p : Positions counts => placedShapeChildProduct F s phi p.1)
    (fun p => Row (phi s) p.1) (fun p => Middle (phi s) p.1)
    (fun p => Column (phi s) p.1) a c e h

end MatrixMultiplication.CWStageCProducts

end

end OAI
