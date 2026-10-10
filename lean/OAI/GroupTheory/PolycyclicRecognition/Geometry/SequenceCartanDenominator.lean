import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntervalDenominator
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ScaleExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootIntervalSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrenceBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The compact support of every original interval law fits into one fixed
translated enlarged box. Its exact Haar-volume ratio is independent of scale. -/
theorem exists_interval_recurrence_denominator_sequence
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (q : Fin M.letterCount → ℝ)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * (M.supportIn T hunimod eW).weightSupport E i)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    {m : ℕ} (letters : Fin m → Fin M.letterCount) :
    ∃ D : ℝ, 1 ≤ D ∧
      let μ := MeasureTheory.Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm)
        MeasureTheory.volume
      ∀ᶠ r in atTop,
        let k₀ := F.ExpN (F.N.equiv (k r))
        let Q := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale r) 1
        let Q' := (fun y => y * k₀) '' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale r) D
        (∀ j : Fin m, ∀ x ∈ Q,
          ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q (scale r) R j.val,
            x * u ∈ Q') ∧
        μ Q' = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ Q := by
  let ε' := extendOnScales scale ε 0
  let k' := extendOnScales scale k 0
  have hε' : Tendsto ε' atTop (𝓝 0) := tendsto_extendOnScales hmono hε
  have hε'pos (t : ℝ) : 0 ≤ ε' t := by
    dsimp [ε', extendOnScales]
    split_ifs
    · exact hεpos _
    · exact le_rfl
  have hk' : ∀ᶠ t : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun (k' t)‖ ≤
          Real.exp (t * ε' t) := by
    apply eventually_extendOnScales hmono k 0
      (fun t y => ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) t).equivFun y‖ ≤
          Real.exp (t * ε' t))
    · intro t
      simp only [map_zero, norm_zero]
      exact (Real.exp_pos _).le
    · simpa only [ε', extendOnScales_apply hmono] using hk
  obtain ⟨D, hD, hbound⟩ := M.exists_interval_recurrence_denominator T F hunimod eW
    hExpG realize haarN dynkinN b₀ E β q hβ hδ hc hhi hR hcost hgap hq
    ε' hε'pos hε' k' hk' letters
  refine ⟨D, hD, ?_⟩
  simpa only [k', extendOnScales_apply hmono] using hscale.eventually hbound

end PolycyclicRecognition.CartanWordModel

end

end OAI
