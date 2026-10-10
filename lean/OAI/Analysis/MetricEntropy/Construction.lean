import OAI.Analysis.MetricEntropy.MatrixEntropy
import OAI.Analysis.MetricEntropy.RobustDirections
import OAI.Analysis.MetricEntropy.FiniteFieldRows
import OAI.Analysis.MetricEntropy.Compression

namespace OAI

/-!
# The unconditional construction with the prime chosen last

The only inputs are the proposed scale, a positive rank, and a positive
entropy budget. The prime, robust directions, contraction partitions,
separated real matrix, positive and signed approximation lists, and actual
convex body are all constructed by the preceding theorems.
-/

noncomputable section

namespace MetricEntropyDuality

/-- Construct actual full-dimensional bodies and their strict entropy bound.
There is no matrix, compression, geometric, or entropy premise. -/
theorem exists_entropy_pair_with_budget (a : ℝ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 1 ≤ r) (B : ℝ) (hB : 0 < B) :
    Nonempty (EntropyPair a r B) := by
  classical
  have hr₀ : 0 < r := hr
  let θ := accuracy a
  let h := compressionRadius a
  let j := h - 1
  have hh : 0 < h := compressionRadius_pos a
  have hj : j + 1 = h := Nat.sub_add_cancel hh
  have hθ : 0 < θ := accuracy_pos ha
  have hθ₁ : θ < 1 := accuracy_lt_one ha
  -- The preceding real and finite quantities are fixed before `p` is selected.
  obtain ⟨p, hp, _, hp_h, hp_size, hp_entropy, _, _, _, _⟩ :=
    exists_prime_for_rank ha hr₀ B 0 hB
  let : Fact p.Prime := ⟨hp⟩
  let u := directionCount r (j + 1) θ
  have hu : 0 < u := directionCount_pos hr₀ (Nat.succ_pos j) hθ
  have hp_h' : j + 1 < p := by simpa only [hj] using hp_h
  have hp_size' : (j + 1) ^ 2 * u ^ (2 * (j + 1)) < p := by
    simpa only [u, hj] using hp_size
  obtain ⟨t, hrobust⟩ := exists_robust_directions
    hr₀ (Nat.succ_pos j) hθ hθ₁ hp_h' hp_size'
  let X := FiniteFieldRows.RowIndex p r (j + 1)
  let Y := FiniteFieldRows.ColumnIndex θ p r (j + 1) u
  let : Nonempty X := ⟨0⟩
  let : Nonempty Y := FiniteFieldRows.columnIndex_nonempty hθ.le p r (j + 1) u
  let L := FiniteFieldRows.labels (j := j) t
  let 𝒯 := FiniteFieldRows.admissibleSets θ u
  let g : Y → X → ℝ := FiniteFieldRows.column (j := j) θ t
  let q := p ^ formDimension r j
  have hq : 0 < q := pow_pos hp.pos _
  have hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q := by
    intro i
    calc
      Nat.card (Set.range (L i)) ≤ Nat.card (SymmetricForm (ZMod p) r j) :=
        Nat.card_le_card_of_injective (fun z : Set.range (L i) => z.val)
          Subtype.val_injective
      _ = q := by rw [Nat.card_eq_fintype_card, card_form_coefficients]
  have hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
    intro T hT
    exact FiniteFieldRows.mem_admissibleSets.mp hT
  have hsθ : 1 ≤ (pivotSlots θ : ℝ) * θ := by
    simpa only [mul_comm] using one_le_mul_pivotSlots hθ
  have hprofile : Real.log 3 / Real.log (((j + 1 : ℕ) : ℝ) + 1) ≤ θ := by
    simpa only [hj] using compressionRadius_log_le ha
  obtain ⟨A, hAne, hcount, hpositive⟩ := uniform_compression
    (L := L) (hlabels := hlabels) (𝒯 := 𝒯) (hu := hu) (hq := hq)
    (hh := Nat.succ_pos j) (hs := pivotSlots_pos hθ) (θ := θ) (hθ := hθ)
    (hsθ := hsθ) (hprofile := hprofile) (hcomp := hcomp)
  have hsigned : UniformApproximation g (6 * θ)
      (SignedCompression.differenceList A) :=
    SignedCompression.uniformApproximation g θ A hpositive
  have hlog := log_card_le_encodingCost hu hq hθ hAne hcount
  have hlog' : Real.log (A.card : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a)) := by
    change Real.log (A.card : ℝ) ≤
      (h : ℝ) * (pivotSlots θ : ℝ) * Real.log ((p : ℝ) ^ formDimension r j) +
        encodingCost h θ (directionCount r h θ)
    simpa only [q, Nat.cast_pow, u, Nat.succ_eq_add_one, hj] using hlog
  have hrows : Fintype.card X = p ^ formDimension r (compressionRadius a) := by
    change Fintype.card (FiniteFieldRows.RowIndex p r (j + 1)) =
      p ^ formDimension r h
    simpa only [hj] using FiniteFieldRows.card_rowIndex p r (j + 1)
  have hcolumns : Fintype.card X ≤ Fintype.card Y :=
    FiniteFieldRows.card_rowIndex_le_columns hθ.le p r (j + 1) u
  have hsep : ∀ x x' : X, x ≠ x' → ∃ y : Y, 1 ≤ |g y x - g y x'| := by
    intro x x' hxx'
    obtain ⟨y, hy⟩ := FiniteFieldRows.exists_column_abs_eq_one t hrobust x x' hxx'
    exact ⟨y, hy.ge⟩
  exact entropyPair_of_matrix a ha r hr₀ B hB p hp hp_entropy g
    hrows hcolumns hsep (SignedCompression.differenceList A) hsigned
    A.card (SignedCompression.differenceList_card_le A) hlog'

end MetricEntropyDuality

end

end OAI
