import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialGoodCells
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfiles

namespace OAI

/-! # Actual Haar good sets from the independently sampled coordinate profiles -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Set
open scoped Manifold ENNReal Topology

/-- The slow diagonal is performed in the original coordinate probability
space. Its image consists of measurable good sheets in the actual translated
exponential cell, with the same subexponential relative mass. -/
theorem exists_exponential_good_profile_cells_sequence
    {L E N I V W : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace N] [ChartedSpace E N] [Group N]
    [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
    [MeasurableSpace N] [BorelSpace N]
    [TopologicalSpace V] [NormedAddCommGroup W]
    (haar : NilpotentExponentialHaarInput E N)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N) (hnil : LieRing.IsNilpotent L)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) N ≃ₜ N) (hchart : ∀ x, chart x = Exp x)
    (X : I → L) (words : Finset (FreeMagma I))
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (β : WordBasisSelections X words)
    (cost : words → ℝ) (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (k : ℕ → N)
    (C : Set (Fin (finrank ℝ L) → ℝ)) (hC : MeasurableSet C)
    (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ∞)
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (profile : ℕ → (Fin (finrank ℝ L) → ℝ) → S) (hprofile : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume C hC0 hCfin) (profile n)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    let sample := fun n y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
      (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) (scale n)).equivFun.symm) y * k n
    ∃ (A : ℕ → Set N) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ sample n '' C) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal) ∧
      (∀ᶠ n in atTop, 0 < (μ (A n)).toReal) ∧
      ∀ n u, u ∈ A n → ∃ y ∈ C, sample n y = u ∧
        ∀ z ∈ K, ‖(profile n y).val z - f.val z‖ < ε n := by
  dsimp only
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  let sample := fun n y => ((Exp ∘ e) ∘ (exponentialRescaleBasis
    (WordBasisSelections.basis X words β) (fun j => cost (β.val j)) (scale n)).equivFun.symm) y * k n
  obtain ⟨B, ε, hB, hBC, hε, hεlim, hmass, _, hgood⟩ :=
    exists_good_cell_profiles_sequence S K hK scale hscale volume (fun _ => C)
      (fun _ => hC) (fun _ => hC0) (fun _ => hCfin) profile hprofile ν hν hf
  let A := fun n => sample n '' B n
  have hratio (n : ℕ) : (μ (A n)).toReal / (μ (sample n '' C)).toReal =
      (volume (B n)).toReal / (volume C).toReal :=
    translated_exponential_cell_ratio haar e hnil Exp hExp chart hchart X words b₀ β
      cost (scale n) (k n) (B n) C
  have hmass' : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal) := by
    simpa only [hratio] using hmass
  refine ⟨A, ε, ?_, ?_, hε, hεlim, hmass', ?_, ?_⟩
  · intro n
    exact (measurableEmbedding_translated_exponential_basis e Exp chart hchart _ (k n)).measurableSet_image.mpr (hB n)
  · intro n
    exact image_mono (hBC n)
  · filter_upwards [hmass'.eventually_pos] with n hn
    exact (div_pos_iff.mp hn).resolve_right (fun h => ENNReal.toReal_nonneg.not_gt h.1) |>.1
  · rintro n u ⟨y, hy, rfl⟩
    exact ⟨y, hBC n hy, rfl, hgood n y hy⟩

end PolycyclicRecognition

end

end OAI
