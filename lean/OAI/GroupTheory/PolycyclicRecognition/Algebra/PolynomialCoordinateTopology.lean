import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # The topology carried by an actual polynomial coordinate group -/

noncomputable section

namespace PolycyclicRecognition.PolynomialCoordinateGroup

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

instance (m : V → V → V) (h : PolynomialGroupLaws m) :
    TopologicalSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (TopologicalSpace V)

instance [MeasurableSpace V] (m : V → V → V) (h : PolynomialGroupLaws m) :
    MeasurableSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (MeasurableSpace V)

instance [MeasurableSpace V] [BorelSpace V] (m : V → V → V) (h : PolynomialGroupLaws m) :
    BorelSpace (PolynomialCoordinateGroup m h) := inferInstanceAs (BorelSpace V)

theorem isTopologicalGroup (m : V → V → V) (h : PolynomialGroupLaws m)
    (hc : Continuous (fun p : V × V => m p.1 p.2)) :
    IsTopologicalGroup (PolynomialCoordinateGroup m h) where
  continuous_mul := hc
  continuous_inv := by
    change Continuous (fun x : V => -x)
    exact continuous_neg

def expHomeomorph (m : V → V → V) (h : PolynomialGroupLaws m) :
    V ≃ₜ PolynomialCoordinateGroup m h where
  toEquiv := exp m h
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

end PolycyclicRecognition.PolynomialCoordinateGroup

end

end OAI
