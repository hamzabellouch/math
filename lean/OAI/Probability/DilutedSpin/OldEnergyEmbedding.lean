import OAI.Probability.DilutedSpin.OneNewLaw
import OAI.Probability.DilutedSpin.PhysicalCavityPoisson

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

noncomputable def liftOldEnergy : (((Fin N → Spin) → ℝ) →L[ℝ] ((Fin (N+1) → Spin) → ℝ)) where
  toFun E σ := E (fun i => σ i.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

lemma old_markLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
      indexedPotential theta (z.1,fun i => (z.2 i).succ))
      (μ.prod (finiteUniform (Fin (q+1) → Fin N)))=
    Measure.map (liftOldEnergy (N := N))
      (Measure.map (indexedPotential theta) (μ.prod (finiteUniform (Fin (q+1) → Fin N)))) := by
  rw [Measure.map_map (liftOldEnergy (N := N)).measurable (measurable_indexedPotential theta hθ)]
  rfl

lemma old_compoundLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (r : ℝ≥0) :
    compoundPoisson r (Measure.map (fun z : X×(Fin (q+1) → Fin N) =>
      indexedPotential theta (z.1,fun i => (z.2 i).succ))
      (μ.prod (finiteUniform (Fin (q+1) → Fin N))))=
    Measure.map (liftOldEnergy (N := N))
      (compoundPoisson r (Measure.map (indexedPotential theta)
        (μ.prod (finiteUniform (Fin (q+1) → Fin N))))) := by
  rw [old_markLaw μ theta hθ,compoundPoisson_map_linear]

end DilutedSpinGlass

end

end OAI
