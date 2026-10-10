import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileCompactness

namespace OAI

/-! # Uniform anchor bounds for translated nilpotent box samples -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Sampling one box and then multiplying by a suffix in a subexponentially
enlarged positive-weight box gives a uniformly bounded normalized distance.
This discharges the metric anchor condition for the chart-profile family. -/
theorem exists_bounded_box_profile_anchors
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s t : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) :
    ∃ B lo : ℝ, 0 ≤ B ∧ 0 < lo ∧ ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ r ε : ℝ, 1 ≤ r → ε ≤ lo → ∀ n k : F.N.carrier,
      n ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent s (β.val j)) r) 1 →
      k ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun j => bracketWordExponent t (γ.val j)) r) (Real.exp (r * ε)) →
      dist 1 (F.inclusionN (n * k)) / r ≤ B := by
  obtain ⟨C, l, hC, hl, hbody⟩ := exists_cartan_n_expanded_metric_bound T M F hExpG
    realize haarN dynkinN b₀ s hs
  obtain ⟨D, lo, hD, hlo, hsuffix⟩ := exists_cartan_n_expanded_metric_bound T M F hExpG
    realize haarN dynkinN b₀ t ht
  refine ⟨2 * (C + D), lo, by positivity, hlo, ?_⟩
  intro β γ hβ hγ r ε hr hε n k hn hk
  rcases hn with ⟨v, rfl, hv⟩
  rcases hk with ⟨w, rfl, hw⟩
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hn := hbody β hβ r 0 hr0 hl.le v (by simpa using hv)
  have hk := hsuffix γ hγ r ε hr0 hε w hw
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hr)).mpr
  rw [map_mul]
  apply (dist_one_mul_le _ _).trans
  dsimp only [Function.comp_apply]
  nlinarith

end PolycyclicRecognition

end

end OAI
