import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanDenominator
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialCellMass
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalPadding
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntervalDenominator
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ScaleExtension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootIntervalSlack
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRecurrenceBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # A fixed recurrence denominator for the actual root interval laws -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter MeasureTheory Set
open scoped Manifold Topology Matrix.Norms.Operator ENNReal

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
theorem exists_interval_recurrence_cells_sequence
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
      let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
      let B := fun n R => (fun y => y * F.ExpN (F.N.equiv (k n))) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) R
      (∀ n, 0 < (μ (B n 1)).toReal ∧ μ (B n 1) ≠ ∞ ∧
        0 < (μ (B n D)).toReal ∧ μ (B n D) ≠ ∞) ∧
      (∀ n, (μ (B n D)).toReal = D ^ finrank ℝ (cartanRootIdeal H) * (μ (B n 1)).toReal) ∧
      ∀ᶠ n in atTop, ∀ j : ℕ, ∀ x ∈ B n 1,
        ∀ u ∈ rootIntervalSupport (F.ExpN ∘ F.N.equiv) letters M.letter q (scale n) R j,
          x * u ∈ B n D := by
  obtain ⟨D, hD, hbound⟩ := M.exists_interval_recurrence_denominator_sequence
    T F hunimod eW hExpG realize haarN dynkinN b₀ E β q hβ hδ hc hhi hR hcost hgap hq
    scale hscale hmono ε hεpos hε k hk letters
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let B := fun n R => (fun y => y * F.ExpN (F.N.equiv (k n))) ''
    M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) R
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : μ.IsMulRightInvariant := exponential_basis_measure_isRightInvariant haarN F.N.equiv hnil F.ExpN F.isExpN b₀
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN (F.N.tangent_nilpotent hnil)
  have hmass (n : ℕ) (R' : ℝ) (hR' : 0 < R') :
      0 < (μ (B n R')).toReal ∧ μ (B n R') ≠ ∞ := by
    have hh := translated_exponential_cell_mass haarN F.N.equiv hnil F.ExpN F.isExpN
      chartN hchartN M.letter M.wordList b₀ β (M.boxCost T hunimod eW E) (scale n)
      (F.ExpN (F.N.equiv (k n))) (Icc (fun _ => -R') (fun _ => R'))
      (coordinate_cube_mass hR').1 (coordinate_cube_mass hR').2
    dsimp only [B, groupBox]
    rw [exponentialCoordinateBox_eq_cube_image _ _ R' hR'.le, ← image_comp]
    exact hh
  refine ⟨D, hD, ?_⟩
  change (∀ n, _) ∧ (∀ n, _) ∧ _
  refine ⟨fun n => ⟨(hmass n 1 zero_lt_one).1, (hmass n 1 zero_lt_one).2,
    (hmass n D (zero_lt_one.trans_le hD)).1, (hmass n D (zero_lt_one.trans_le hD)).2⟩, ?_, ?_⟩
  · intro n
    have he : μ (B n D) = ENNReal.ofReal (D ^ finrank ℝ (cartanRootIdeal H)) * μ (B n 1) := by
      dsimp only [B]
      rw [measure_image_mul_right μ, measure_image_mul_right μ]
      exact exponential_box_radius_measure F.N.equiv F.ExpN chartN hchartN b₀
        (M.boxBasis T hunimod eW E β (scale n)) (zero_le_one.trans hD)
    rw [he, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (zero_le_one.trans hD) _)]
  · filter_upwards [hbound] with n hn
    apply rootIntervalSupport_mul_mem_padded (F.ExpN ∘ F.N.equiv)
      (by simp [F.isExpN.map_zero]) letters M.letter q (scale n) R hR ?_ hn.1
    apply image_mono
    rintro x ⟨v, hv, hnorm⟩
    exact ⟨v, hv, hnorm.trans hD⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
