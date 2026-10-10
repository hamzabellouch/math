import OAI.Probability.DilutedSpin.MeasurableShapeEnergy
import OAI.Probability.DilutedSpin.ParameterRate

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n : ℕ}

section Shape
variable (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (Q : (i : I) → Fin (n+1+d) → FiniteLaw (A i))
    (m : Fin (n+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+d) → FinitePath (A i) (n+1+d) → ℝ)
    (V : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootShapeEnergy : Measurable (fun z : FullRootState Y X I M =>
    shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) := by
  change Measurable (packRoot (fun h k x n y =>
    shapeEnergyAt C d (KernelTower.tilt _ (tower (rootArray n y) _ T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) _ w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_shapeEnergyAt_tilt C d (tower (rootArray n y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
lemma integrable_rootShapeEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) μ := by
  apply Integrable.of_bound (measurable_rootShapeEnergy C d T Q m base old V hb).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (shapeEnergyAt_nonneg C d _ _)]
  exact shapeEnergyAt_le_four C d _ _ (fun y i => hV _ i)
end Shape

section Child
variable (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (Q : (i : I) → Fin (n+1+r+1+d) → FiniteLaw (A i))
    (m : Fin (n+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+r+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+r+1+d) → FinitePath (A i) (n+1+r+1+d) → ℝ)
    (V : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootDescendantEnergy : Measurable (fun z : FullRootState Y X I M =>
    descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z)) := by
  change Measurable (packRoot (fun h k x n y =>
    descendantEnergyAt C r d (KernelTower.tilt _ (tower (rootArray n y) _ T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) _ w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_descendantEnergyAt_tilt C r d (tower (rootArray n y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
lemma integrable_rootDescendantEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z)) μ := by
  apply Integrable.of_bound (measurable_rootDescendantEnergy C r d T Q m base old V hb).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (descendantEnergyAt_nonneg C r d _ _)]
  exact descendantEnergyAt_le_four C r d _ _ (fun y i => hV _ i)

include hb in
lemma integrable_sqrt_rootDescendantEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      Real.sqrt (descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z))) μ := by
  apply Integrable.of_bound (measurable_rootDescendantEnergy C r d T Q m base old V hb).sqrt.aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := Real.sqrt_le_sqrt (descendantEnergyAt_le_four C r d
    (rootTower T Q m base old z) (rootVector V z) (fun y i => hV _ i))
  norm_num at h
  exact h
end Child

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
