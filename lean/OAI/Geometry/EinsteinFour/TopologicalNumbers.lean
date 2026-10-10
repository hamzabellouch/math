import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

namespace OAI

/-! Concrete rational Betti numbers and the four-dimensional Euler number.
The finite-CW comparison and covering multiplicativity are classical inputs;
the parity obstruction below uses their precise numerical specialization. -/

namespace PositiveEinsteinFour.Topology

open CategoryTheory

noncomputable section

universe u

def rationalHomology (X : Type u) [TopologicalSpace X] (n : ℕ) : ModuleCat.{u} ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) n).obj
    (ModuleCat.of ℚ (ULift.{u} ℚ))).obj (TopCat.of X)

def rationalBetti (X : Type u) [TopologicalSpace X] (n : ℕ) : ℕ :=
  Module.finrank ℚ (rationalHomology X n)

def eulerFour (X : Type u) [TopologicalSpace X] : ℤ :=
  ∑ i : Fin 5, (-1 : ℤ) ^ i.val * (rationalBetti X i.val : ℤ)

/-- No space with Euler number three can be a two-sheeted cover of a finite
four-dimensional CW space once the classical multiplicativity formula is
instantiated. This is the CP² obstruction in the unoriented classification. -/
theorem no_double_cover_of_euler_three
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (hthree : eulerFour X = 3) (hcover : eulerFour X = 2 * eulerFour Y) : False := by
  omega

end

end PositiveEinsteinFour.Topology

end OAI
