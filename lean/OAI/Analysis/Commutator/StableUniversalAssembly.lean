import Mathlib
import OAI.Analysis.Commutator.InfiniteBoundTransfer
import OAI.Analysis.Commutator.SeparableUniverseTransfer
import OAI.Analysis.Commutator.StableCentralSpectral
import OAI.Analysis.Commutator.StableModelBound

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

theorem separable_uniform_bound : SeparableTest.SeparableBound.{0} 9368 := by
  intro H _ _ _ _ M Y h hh X hX
  obtain ⟨μ,hμ,U,hU,hind,hsep⟩ := exists_stable_center_spectral_model M
  let : IsFiniteMeasure μ := hμ
  let : TopologicalSpace.SeparableSpace (Space ℕ ℂ) := separable_space
  let : TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ) := hsep
  apply bound_of_stable_bound M Y h X hX (by norm_num)
  exact stable_model_bound M μ U hU hind (map Y) h hh (fun i j => map (ι:=ℕ) (X i j))
    (fun i j => map_mem_algebra M _ (hX i j))

theorem universal_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
  SeparableTest.bound_of_small_separable_bound P Y h hh X hX (by norm_num) separable_uniform_bound

end Kadison.CentralSpectral

end

end
end

end OAI
