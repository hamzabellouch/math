import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import Mathlib.Algebra.CharP.Algebra

namespace OAI

/-! The concrete Laurent coefficient ring is a characteristic-zero domain.
These instances are consequences of its actual localization construction. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

instance laurentCoefficients_isDomain : IsDomain LaurentCoefficients :=
  Localization.Away.isDomain (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℂ) ≠ 0)

instance laurentCoefficients_charZero : CharZero LaurentCoefficients :=
  charZero_of_injective_algebraMap (algebraMap ℂ LaurentCoefficients).injective

end AbhyankarSathaye.CommutingDerivations

end

end OAI
