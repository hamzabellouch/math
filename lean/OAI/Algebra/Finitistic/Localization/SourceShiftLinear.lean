import OAI.Algebra.Finitistic.Localization.SourceLinear

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

/-- Scalar action commutes with shifts on bounded projective homotopy complexes. -/
instance shiftLinearK (n : ℤ) : (shiftFunctor (K P) n).Linear k := by
  let I := (BoundedHomotopy.bounded (Proj P)).ι
  have : (shiftFunctor (K P) n ⋙ I).Linear k :=
    Functor.linear_of_iso k (I.commShiftIso n).symm
  constructor
  intro X Y f a
  apply I.map_injective
  rw [I.map_smul]
  exact (shiftFunctor (K P) n ⋙ I).map_smul a f

/-- Scalar action commutes with shifts on the actual source Verdier quotient. -/
instance shiftLinearQ (n : ℤ) : (shiftFunctor (Q P) n).Linear k := by
  let : Localization.Lifting (q P) (Sigma P)
      (shiftFunctor (K P) n ⋙ q P) (shiftFunctor (Q P) n) :=
    ⟨((q P).commShiftIso n).symm⟩
  exact (Localization.functor_linear_iff (q P) (Sigma P) k
    (shiftFunctor (K P) n ⋙ q P) (shiftFunctor (Q P) n)).mp inferInstance

end LittleFinitistic.SourceVerdier

end

end OAI
