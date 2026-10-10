import OAI.Geometry.EinsteinFour.TopologicalNumbers

namespace OAI

/-! Transport of the actual rational singular-homology dimensions through
homeomorphisms.  No metric identification or topological model computation
is presumed by these statements. -/

namespace PositiveEinsteinFour.Topology

open CategoryTheory

noncomputable section

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The singular-homology functor turns a homeomorphism into a rational
linear equivalence in every degree. -/
def rationalHomologyCongr (h : X ≃ₜ Y) (n : ℕ) :
    rationalHomology X n ≃ₗ[ℚ] rationalHomology Y n :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) n).obj
    (ModuleCat.of ℚ (ULift.{u} ℚ))).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) h)).toLinearEquiv

theorem rationalBetti_homeomorph (h : X ≃ₜ Y) (n : ℕ) :
    rationalBetti X n = rationalBetti Y n :=
  (rationalHomologyCongr h n).finrank_eq

theorem eulerFour_homeomorph (h : X ≃ₜ Y) : eulerFour X = eulerFour Y := by
  unfold eulerFour
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalBetti_homeomorph h i.val]

end
end PositiveEinsteinFour.Topology

end OAI
