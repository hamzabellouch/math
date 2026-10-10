import Mathlib
import OAI.Analysis.Commutator.AbelianGNSSpectral
import OAI.Analysis.Commutator.UnitaryCenterTransport
import OAI.Analysis.Commutator.StableCenterRange
import OAI.Analysis.Commutator.StableScalarGeometry

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable InfiniteAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (μ : Measure (Spectrum M))

variable (U : Space ℕ H ≃ₗᵢ[ℂ] Lp (Space ℕ ℂ) 2 μ)

variable (hU : ∀ (a : CentralCorner.center M) (v : Space ℕ H),
  U (map (a : H →L[ℂ] H) v)=scalarVectorMultiplier μ (gelfandStarTransform _ a) (U v))

include hU

lemma conjugate_center (a : CentralCorner.center M) :
    U.conjStarAlgEquiv (map a.val)=scalarVectorMultiplier μ (gelfandStarTransform _ a) := by
  apply ContinuousLinearMap.ext
  intro v
  change U (map a.val (U.symm v))=scalarVectorMultiplier μ (gelfandStarTransform _ a) v
  rw [hU,U.apply_symm_apply]

lemma central_indicators
    (hind : ∀ (s : Set (Spectrum M)) (hs : MeasurableSet s),
      ∃ a : CentralCorner.center M,
        scalarMultiplier μ (gelfandStarTransform _ a)=indicatorOperator μ s hs)
    (s : Set (Spectrum M)) (hs : MeasurableSet s) :
    indicatorOperator (H:=Space ℕ ℂ) μ s hs ∈
      CentralCorner.center (UnitaryTransport.algebra U (algebra M)) := by
  obtain ⟨a,ha⟩ := hind s hs
  rw [←vector_indicator_of_scalar μ _ s hs ha,←conjugate_center M μ U hU a]
  exact (UnitaryTransport.mem_center_algebra U (algebra M) (map a.val)).mpr
    ((map_mem_center M a.val).mpr a.property)

lemma center_commutes_constant
    (Z : Lp (Space ℕ ℂ) 2 μ →L[ℂ] Lp (Space ℕ ℂ) 2 μ)
    (hZ : Z∈CentralCorner.center (UnitaryTransport.algebra U (algebra M)))
    (C : Space ℕ ℂ →L[ℂ] Space ℕ ℂ) :
    Commute (operator μ (fun _ => C) (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall (fun _ => le_rfl))) Z := by
  obtain ⟨a,ha⟩ := stable_center_range M U Z hZ
  rw [←ha,conjugate_center M μ U hU a]
  exact scalarVectorMultiplier_commutes_constant μ _ C

end Kadison.CentralSpectral

end

end
end

end OAI
