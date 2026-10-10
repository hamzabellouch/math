import OAI.RepresentationTheory.FoulkesHowe.TensorPresentation

namespace OAI

noncomputable section
universe u

namespace Problem346

/-- Every homogeneous symmetric power of a finite-dimensional complex space is
finite dimensional. The proof uses its tensor-power presentation. -/
instance finiteDimensional_symPow (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] : FiniteDimensional ℂ (SymPow n V) :=
  Module.Finite.of_surjective (tensorToSymPow n V) (tensorToSymPow_surjective n V)

end Problem346

end

end OAI
