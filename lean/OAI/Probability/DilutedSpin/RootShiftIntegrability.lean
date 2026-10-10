import OAI.Probability.DilutedSpin.MeasurableProjector
import OAI.Probability.DilutedSpin.ParameterRate
import OAI.Probability.DilutedSpin.RootProjectionShiftError

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ReducedTopology
open scoped BigOperators
attribute [local irreducible] ReducedTopology.projectionShiftError
variable {Ω I X Y α ι : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype α] [DecidableEq α] [Fintype ι]
    {L M N : ℕ} [NeZero L]

variable (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (P : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- The exact single-copy shift error is measurable at the physical root,
including all Poisson counts and its countable variable marker alphabet. -/
lemma measurable_root_projectionShiftError (Q : α → Fin L) :
    Measurable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) := by
  change Measurable (packRoot (fun h k x n y =>
    projectionShiftError a C e
      (KernelTower.tilt L (tower (rootArray n y) L T P) m
        (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) L w)) Q))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_projectionShiftError_tilt a C e (tower (rootArray n y) L T P) m ?_ ?_ Q
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma integrable_root_projectionShiftError (μ : Measure (FullRootState Y X I M))
    [IsFiniteMeasure μ] (hV : ∀ y i, |V y i|≤1) (Q : α → Fin L) :
    Integrable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) μ := by
  apply Integrable.of_bound (measurable_root_projectionShiftError a C e T P m base old V hb Q).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (projectionShiftError_nonneg a C e _ _ Q)]
  exact projectionShiftError_le_four a C e _ _ (fun y i => hV _ i) Q

include hb in
 
theorem physical_root_shift_average (μ : Measure (FullRootState Y X I M))
    [IsProbabilityMeasure μ] (hV : ∀ y i, |V y i|≤1)
    (he : ∀ j, Function.Injective (e j)) (η : ℝ) (hlarge : 1<η*(L:ℝ))
    (D : (α → Fin L) → Prop)
    (hD : ∀ Q, D Q → ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) ((Q a).val+1) L ∧
      DepthAverage.Regular η (fun v => Q (e j v))) :
    DepthAverage.average D (fun Q => ∫ z,
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q ∂μ) ≤
      Real.sqrt (8*((Fintype.card ι:ℝ)*(∑ j, (Fintype.card (C j).Vertex:ℝ)*
        (∑ v : (C j).Vertex, (ReducedTopology.vertexArity (C j) v:ℝ)^2))+
          (Fintype.card ι:ℝ)^2)/(L:ℝ)) := by
  apply root_averaged_projectionShiftError_le μ
    (rootAlphabet (Ω := Ω) (A := A)) a C e he η hlarge D hD
    (rootTower T P m base old) (rootVector V) (fun z y i => hV _ i)
  exact integrable_root_projectionShiftError a C e T P m base old V hb μ hV

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
