import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference
import OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveEmbeddingCohomologyBound

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_of_le_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d e : ℕ) (hde : d ≤ e)
    (hzero : ∀ q : ℕ, d < q → ∀ z : cohomology M q, z = 0) :
    eulerCharacteristic p e M = eulerCharacteristic p d M := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih =>
    calc
      eulerCharacteristic p (e+1) M = eulerCharacteristic p e M := by
        simpa only [Nat.add_sub_cancel] using
          eulerCharacteristic_eq_pred_of_cohomology_zero p M (e+1)
            (hzero (e+1) (by omega))
      _ = eulerCharacteristic p d M := ih

theorem eulerCharacteristic_projective_eq_dimension
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H : LineBundle X) (hH : H.IsAmple) (M : LineBundle X)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    eulerCharacteristic p r M.sheaf = eulerCharacteristic p d M.sheaf := by
  let : IsProper p := by rw [← hi]; infer_instance
  rcases le_total d r with h | h
  · exact eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf d r h
      (lineBundle_cohomology_zero_of_dimension_le d p H hH M hdim)
  · symm
    apply eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf r d h
    intro q hq z
    exact lineBundle_cohomology_eq_zero_of_projective_embedding r i M q (by omega) z

end
end PiExponent.NumericalAmpleness

end OAI
