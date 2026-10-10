import OAI.GroupTheory.PolycyclicRecognition.Analysis.MixedWordBoxModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput

namespace OAI

/-! # Product and Haar estimates for the actual cone ideal boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory
open scoped Manifold BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealBoxBasis (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r : ℝ) :
    Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C) :=
  exponentialRescaleBasis
    (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
    (fun j => M.coneIdealWordCost C s (β.val j)) r

def coneIdealBox {G : Type*} (Exp : M.coneWordIdeal C → G)
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r R : ℝ) : Set G :=
  exponentialCoordinateBox Exp (M.coneIdealBoxBasis C s β r) R

def IsMaximizingConeIdealBasis
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) : Prop :=
  IsMaximizingColumnBasis
    (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀)
    (fun w => M.coneIdealWordCost C s w) β.val

theorem exists_maximizing_coneIdealBasis
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) :
    ∃ β, M.IsMaximizingConeIdealBasis C b₀ s β :=
  exists_maximizing_wordBasis _ _ b₀ _

theorem coneIdealWordCost_smul (s : Fin M.letterCount → ℝ) (t : ℝ)
    (w : FreeMagma (M.coneMixedWords C)) :
    M.coneIdealWordCost C (fun i => t * s i) w = t * M.coneIdealWordCost C s w := by
  rw [M.coneIdealWordCost_eq_original, M.coneIdealWordCost_eq_original]
  simp only [bracketWordExponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem maximizing_coneIdealBasis_smul
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) {t : ℝ} (ht : 0 ≤ t) :
    M.IsMaximizingConeIdealBasis C b₀ (fun i => t * s i) β := by
  refine ⟨hβ.1, ?_⟩
  intro d hd
  simp only [columnBasisWeight, M.coneIdealWordCost_smul, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hβ.2 d hd) ht

theorem exists_uniform_coneIdeal_structureConstant_bound
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s β → ∀ r : ℝ, 0 ≤ r →
      ∀ i j k, |(M.coneIdealBoxBasis C s β r).repr
        ⁅M.coneIdealBoxBasis C s β r i, M.coneIdealBoxBasis C s β r j⁆ k| ≤ K := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_rescaled_structureConstant_bound
    (M.coneMixedVector C) (M.coneIdealWordBound_zero C) b₀
  exact ⟨K, hK, fun s β hβ r hr =>
    hb (fun w => bracketWordExponent s w.val.val) β hβ r hr⟩

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
theorem exists_coneIdealBox_product_bound (dynkin : NilpotentDynkinExpansionInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
      M.IsMaximizingConeIdealBasis C b₀ s β →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → G,
      (∀ i, g i ∈ M.coneIdealBox C (Exp ∘ e) s β r R) →
      (List.ofFn g).prod ∈ M.coneIdealBox C (Exp ∘ e) s β r
        (K * (1 + (n : ℝ)) ^ M.coneIdealWordBound C *
          (1 + R) ^ M.coneIdealWordBound C) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_word_box_product_bound dynkin e Exp hExp
    (M.coneMixedVector C) (M.coneIdealWordBound_zero C) b₀
  exact ⟨K, hK, fun s β hβ r hr n R hR g hg =>
    hb (fun w => bracketWordExponent s w.val.val) β hβ r hr n R hR g hg⟩

omit [T2Space G] in
include hExp in
theorem coneIdealBox_inv_mem (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (r R : ℝ) {g : G} (hg : g ∈ M.coneIdealBox C (Exp ∘ e) s β r R) :
    g⁻¹ ∈ M.coneIdealBox C (Exp ∘ e) s β r R :=
  inv_mem_exponentialCoordinateBox e Exp hExp (M.coneIdealBoxBasis C s β r) hg

variable [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]

include hExp in
/-- The ideal volume exponent is the sum of the original mixed-word widths.
The formula holds for every selected basis, before maximizing. -/
theorem exists_coneIdealBox_haar_volume (haar : NilpotentExponentialHaarInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r R : ℝ), 0 ≤ R →
      μ (M.coneIdealBox C (Exp ∘ e) s β r R) =
        ENNReal.ofReal |(columnBasisMatrix
          (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀)
          β.val).det| *
        ENNReal.ofReal (Real.exp (r * ∑ j,
          bracketWordExponent s (M.coneOriginalWord C (β.val j)))) *
        ENNReal.ofReal (2 * R) ^ finrank ℝ (M.coneWordIdeal C) := by
  obtain ⟨μ, hμ, hv⟩ := exists_haar_measure_model_weighted_boxes haar Exp hExp e
    (M.coneIdeal_nilpotent C) (M.coneMixedVector C) (M.coneIdealWordList C) b₀
  refine ⟨μ, hμ, ?_⟩
  intro s β r R hR
  have hh := hv (fun w => M.coneIdealWordCost C s w) β r R hR
  change μ (M.coneIdealBox C (Exp ∘ e) s β r R) = _ at hh
  simpa only [columnBasisWeight, M.coneIdealWordCost_eq_original] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
