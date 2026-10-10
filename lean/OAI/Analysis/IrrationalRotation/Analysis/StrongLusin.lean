import OAI.Analysis.IrrationalRotation.Analysis.SimultaneousLusin
import OAI.Analysis.IrrationalRotation.Analysis.StrongContinuityFromColumns

namespace OAI

open Set MeasureTheory
open scoped ENNReal

namespace Invariant233.StrongLusin

theorem exists_compact_strong_continuousOn {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [Countable ι] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, Measurable (fun x => A x (b i)))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      ∀ v : E, ContinuousOn (fun x => A x v) Q := by
  obtain ⟨Q, hQ, hsmall, hcont⟩ :=
    SimultaneousLusin.exists_compact_forall_continuousOn μ
      (fun i x => A x (b i)) hcolumns hε
  exact ⟨Q, hQ, hsmall, fun v =>
    StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
      (fun x _ => hbound x) b hcont v⟩

theorem exists_compact_strong_and_continuousOn {𝕜 X E F ι J : Type*}
    {Y : J → Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [∀ j, TopologicalSpace (Y j)] [∀ j, MeasurableSpace (Y j)]
    [∀ j, OpensMeasurableSpace (Y j)] [∀ j, SecondCountableTopology (Y j)]
    [Countable ι] [Countable J] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, Measurable (fun x => A x (b i)))
    (g : ∀ j, X → Y j) (hg : ∀ j, Measurable (g j))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      (∀ v : E, ContinuousOn (fun x => A x v) Q) ∧
      ∀ j, ContinuousOn (g j) Q := by
  have hmeas : Measurable (fun x => ((fun i => A x (b i)), (fun j => g j x))) :=
    (Measurable.of_eval hcolumns).prodMk (Measurable.of_eval hg)
  obtain ⟨Q, hQ, hsmall, hcont⟩ :=
    SimultaneousLusin.exists_compact_continuousOn μ hmeas hε
  refine ⟨Q, hQ, hsmall, ?_, continuousOn_pi.mp hcont.snd⟩
  exact fun v => StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
    (fun x _ => hbound x) b (continuousOn_pi.mp hcont.fst) v

end Invariant233.StrongLusin

end OAI
