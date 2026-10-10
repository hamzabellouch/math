import OAI.Analysis.KadisonKastler.CommonCyclicSubalgebra
import OAI.Analysis.KadisonKastler.NormalMatrixImage

namespace OAI

/-! # The common matrix generators in the faithful cyclic representation -/

namespace KadisonKastler

noncomputable section

open Generator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (A : ℕ → FiniteMatrixStage R)

omit [Nontrivial H] in
theorem cyclicCommonMatrixUnits_mono
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    Monotone (fun n => (normalImageMatrixUnits (cyclicCommonHom M R hRM) A n).algebra) :=
  normalImageMatrixUnits_mono (cyclicCommonHom M R hRM) A hA

omit [Nontrivial H] in
theorem cyclicCommonMatrixUnits_generated
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hgen : FiniteMatrixStage.generatedVonNeumann A = R) :
    cyclicCommonAlgebra M R hRM = generatedVonNeumannAlgebra
      (⨆ n, (normalImageMatrixUnits (cyclicCommonHom M R hRM) A n).algebra) :=
  (normalImageMatrixUnits_generated (cyclicCommonHom M R hRM) A
    (cyclicCommonHom_normal M R hRM) hA hgen).symm

end

end KadisonKastler

end OAI
