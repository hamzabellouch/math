import OAI.Analysis.KadisonKastler.PointedPowerMoments
import OAI.Analysis.KadisonKastler.PointedProductLift
import OAI.Analysis.KadisonKastler.PointedOperationsAssembly

namespace OAI

/-! # Concrete Powers product and the pointed-product input

The countable configuration Hilbert space carries the faithful product
of the two-dimensional diagonal state. Its commuting right action gives
a separating vacuum; finite configuration vectors give cyclicity.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- A constant two-dimensional product with its actual matrix-state moments. -/
def constantPointedMatrixProduct {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    PointedMatrixProduct.{0} (fun _ : ℕ => ν) := by
  let d : PointedLocalMatrixData ν := Classical.choice (exists_pointedLocalMatrixData hν)
  exact {
    K := PointedPowerHilbert
    algebra := pointedPowerAlgebra d.left
    vector := pointedPowerVacuum
    coordinates := {
      valid := fun _ => ⟨hν,hν1⟩
      site := pointedPowerSite d.left
      commuting := pointedPowerSite_commuting d.left
      generates := rfl
      unit_vector := norm_pointedPowerVacuum
      cyclic := pointedPowerAlgebra_cyclic d.left d.left_spans
      separating := pointedPowerAlgebra_separating d
      moments := pointedPower_moments d } }

/-- The fixed lambda product required by the absorption argument. -/
def fixedPowersProduct : PointedMatrixProduct.{u} (fun _ : ℕ => fixedProductLambda) :=
  (constantPointedMatrixProduct fixedProductLambda_pos fixedProductLambda_lt_one).universeLift

/-- Blackadar III.3.1.1--2, specialized to the exact operations used here. -/
theorem publishedPointedMatrixOperations : PublishedPointedMatrixOperations.{u} :=
  publishedPointedMatrixOperations_of_powers ⟨fixedPowersProduct⟩

end

end KadisonKastler

end OAI
