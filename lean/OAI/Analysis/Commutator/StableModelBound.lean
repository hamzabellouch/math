import Mathlib
import OAI.Analysis.Commutator.CentralSpectralGeometry
import OAI.Analysis.Commutator.CentralSpectralModel
import OAI.Analysis.Commutator.InfiniteSeparable
import OAI.Analysis.Commutator.UnitaryBoundTransfer

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (μ : Measure (Spectrum M))

variable (U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ)

variable (hU : ∀ (a : CentralCorner.center M) (v : Space ℕ H),
  U (map (a : H →L[ℂ] H) v)=scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v))

variable (hind : ∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
  ∃ a : CentralCorner.center M,
    scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs)

include hU hind

lemma stable_model_indicators [IsFiniteMeasure μ] (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    indicatorOperator (H:=Space ℕ ℂ) μ s hs∈UnitaryTransport.algebra U (algebra M) ∧
    indicatorOperator (H:=Space ℕ ℂ) μ s hs∈Set.centralizer
      (UnitaryTransport.algebra U (algebra M) : Set _) :=
  (CentralCorner.mem_center _ _).mp (central_indicators M μ U hU hind s hs)

omit hind in
lemma stable_model_center [IsFiniteMeasure μ] (Z : Lp (Space ℕ ℂ) 2 μ →L[ℂ] Lp (Space ℕ ℂ) 2 μ)
    (hZ : Z∈UnitaryTransport.algebra U (algebra M))
    (hZc : Z∈(UnitaryTransport.algebra U (algebra M)).commutant)
    (C : Space ℕ ℂ →L[ℂ] Space ℕ ℂ) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) Z :=
  center_commutes_constant M μ U hU Z ⟨hZ,hZc⟩ C

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace (Lp (Space ℕ ℂ) 2 μ)]

lemma stable_model_bound (Y : Space ℕ H →L[ℂ] Space ℕ H)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (Space ℕ H →L[ℂ] Space ℕ H))
    (hX : ∀ i j,X i j∈algebra M) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm (algebra M) Y*‖matrixOperator h X‖ := by
  let : TopologicalSpace.SeparableSpace (Space ℕ ℂ) := separable_space
  apply UnitaryTransport.bound_of_conjugate_bound U (algebra M) Y h X 9368
  exact uniform_commutator_in_central_spectral_model μ (UnitaryTransport.algebra U (algebra M))
    (stable_model_indicators M μ U hU hind) (stable_model_center M μ U hU)
    (U.conjStarAlgEquiv Y) h hh (fun i j => U.conjStarAlgEquiv (X i j))
    (fun i j => (UnitaryTransport.mem_algebra U (algebra M) _).mpr (hX i j))

end Kadison.CentralSpectral

end

end
end

end OAI
