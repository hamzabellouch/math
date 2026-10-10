import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealTiling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealInnerHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialVolumeRatio

namespace OAI

/-! # The exact exponential bound for ideal-box tilings -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module MeasureTheory Set
open scoped Manifold ENNReal Pointwise

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)

include hExp in
/-- A single Haar normalization supplies both the ambient-inner invariance
and the exact tiling exponent. The radius is independent of the widths,
scale, maximizing basis and automorphism. -/
theorem exists_coneIdeal_measured_tiling
    (haar : NilpotentExponentialHaarInput E G)
    (dynkin : NilpotentDynkinExpansionInput E G)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ (μ : Measure G) (hbij : Function.Bijective Exp) (R : ℝ),
      μ.IsHaarMeasure ∧ 0 < R ∧
      (∀ x : cartanRootIdeal H,
        MeasurePreserving (exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C x)) μ μ) ∧
      ∀ (s₁ s₂ : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C),
        M.IsMaximizingConeIdealBasis C b₀ s₁ β →
        M.IsMaximizingConeIdealBasis C b₀ s₂ β → ∀ r : ℝ, 0 ≤ r →
        ∀ F : G ≃ₜ* G, MeasurePreserving F μ μ →
        F '' M.coneIdealBox C (Exp ∘ e) s₂ β r 1 ⊆
          M.coneIdealBox C (Exp ∘ e) s₁ β r 1 →
        ∃ (n : ℕ) (anchor : Fin n → G) (tile : Fin n → Set G),
          (∀ i, anchor i ∈ M.coneIdealBox C (Exp ∘ e) s₁ β r 1) ∧
          (∀ i, MeasurableSet (tile i)) ∧
          Pairwise (fun i j => Disjoint (tile i) (tile j)) ∧
          (⋃ i, tile i) = M.coneIdealBox C (Exp ∘ e) s₁ β r 1 ∧
          (∀ i, tile i ⊆ anchor i • (F '' M.coneIdealBox C (Exp ∘ e) s₂ β r R)) ∧
          (n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) *
            Real.exp (r * (columnBasisWeight (fun w : M.coneIdealWordList C =>
              M.coneIdealWordCost C s₁ w) β.val -
                columnBasisWeight (fun w : M.coneIdealWordList C =>
                  M.coneIdealWordCost C s₂ w) β.val)) := by
  obtain ⟨μ, hbij, hμ, hinv, hvol⟩ :=
    M.exists_coneIdeal_inner_invariant_haar C e Exp hExp haar b₀
  have hnil := e.nilpotent_iff_equiv_nilpotent.mp (M.coneIdeal_nilpotent C)
  obtain ⟨⟨chart, hchart⟩, _⟩ := haar.2 Exp hExp hnil
  obtain ⟨R, hR, htiles⟩ := M.exists_coneIdeal_tiling_radius C e Exp hExp dynkin chart hchart b₀
  refine ⟨μ, hbij, R, hμ, hR, hinv, ?_⟩
  intro s₁ s₂ β hβ₁ hβ₂ r hr F hF hsmall
  have hdet : 0 < |(columnBasisMatrix
      (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀) β.val).det| :=
    abs_pos.mpr (wordBasis_det_ne_zero _ _ b₀ β)
  have hpos : μ (M.coneIdealBox C (Exp ∘ e) s₂ β r 1) ≠ 0 := by
    rw [hvol s₂ β r 1 zero_le_one]
    simp only [mul_one]
    positivity
  obtain ⟨n, anchor, tile, ha, ht, hd, hu, hs, hn⟩ :=
    htiles s₁ s₂ β hβ₁ hβ₂ r hr μ hμ F hF hsmall hpos
  refine ⟨n, anchor, tile, ha, ht, hd, hu, hs, ?_⟩
  rw [hvol s₂ β r 1 zero_le_one, hvol s₁ β r R hR.le] at hn
  simp only [mul_one] at hn
  have hc := card_le_of_exponential_box_volume hdet hR.le hn
  simpa only [mul_sub] using hc

end PolycyclicRecognition.CartanWordModel

end

end OAI
