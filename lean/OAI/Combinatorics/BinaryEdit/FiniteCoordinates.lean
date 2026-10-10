import OAI.Combinatorics.BinaryEdit.FiniteVectors

namespace OAI

/-!
# Cyclic leaf coordinates

The obstruction averages over the coordinate cyclic groups of the concrete
finite parameter space. Coordinate homomorphisms have exact generators
and a natural-multiple representation.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteVectors

variable {m k : ℕ}

/-- Insertion into one factor of the manuscript's product of cyclic groups. -/
def leafCoordinate (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    ZMod (leafPeriod p a) →+ State p where
  toFun := Pi.single (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a
  map_zero' := Pi.single_zero (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a
  map_add' := Pi.single_add (f := fun b : Leaf m k => ZMod (leafPeriod p b)) a

@[simp] theorem leafCoordinate_apply_self (p : Fin k → Fin m → ℕ)
    (a : Leaf m k) (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z a = z :=
  Pi.single_eq_same (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a z

@[simp] theorem leafCoordinate_apply_ne (p : Fin k → Fin m → ℕ)
    (a b : Leaf m k) (h : b ≠ a) (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z b = 0 :=
  Pi.single_eq_of_ne (M := fun b : Leaf m k => ZMod (leafPeriod p b)) h z

/-- Each cyclic coordinate is genuinely embedded in the parameter group. -/
theorem leafCoordinate_injective (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    Function.Injective (leafCoordinate p a) := by
  intro z z' h
  have heq := congrFun h a
  simpa only [leafCoordinate_apply_self] using heq

/-- The coordinate generator is exactly the already constructed leaf vector. -/
@[simp] theorem leafCoordinate_one (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    leafCoordinate p a 1 = w p k a := by
  funext b
  rw [w_leaf]
  by_cases hab : b = a
  · subst b
    simp
  · simp [hab]

/-- Every residue shift is among the natural multiples of the leaf vector.
This transports the manuscript's pointwise leaf-cost bound to the whole
cyclic-coordinate average used in the spectral estimate. -/
theorem leafCoordinate_eq_val_nsmul (p : Fin k → Fin m → ℕ) (a : Leaf m k)
    [NeZero (leafPeriod p a)] (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z = z.val • w p k a := by
  have hz : z.val • (1 : ZMod (leafPeriod p a)) = z := by
    simp
  calc
    leafCoordinate p a z = leafCoordinate p a (z.val • 1) := congrArg _ hz.symm
    _ = z.val • leafCoordinate p a 1 := map_nsmul _ _ _
    _ = z.val • w p k a := by rw [leafCoordinate_one]

/-- Equivalent integer-multiple formulation, matching the source's allowed
integer leaf translations. -/
theorem leafCoordinate_eq_val_zsmul (p : Fin k → Fin m → ℕ) (a : Leaf m k)
    [NeZero (leafPeriod p a)] (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z = (z.val : ℤ) • w p k a := by
  simpa only [natCast_zsmul] using leafCoordinate_eq_val_nsmul p a z

end TreeEdit.BinaryLower.FiniteVectors

end

end OAI
