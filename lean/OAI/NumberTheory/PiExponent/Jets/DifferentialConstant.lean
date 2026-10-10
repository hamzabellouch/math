import OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction

namespace OAI

namespace PiExponent

open KaehlerDifferential

theorem isAlgebraic_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) : IsAlgebraic C x :=
  isAlgebraic_of_logarithmic_differential (0 : E) x (by simp [hx])

theorem constant_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) :
    ∃ c : C, algebraMap C E c = x :=
  constant_of_logarithmic_differential (0 : E) x (by simp [hx])

end PiExponent

end OAI
