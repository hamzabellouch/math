import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights
import OAI.NumberTheory.Ostmann.Arithmetic.MovingScalarWindows
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularSlots

namespace OAI

/-! # The two initial logarithmic weights as external bulk factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingBulkListLogWeight {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (cb cd : ℝ) (bulk : List σ) : ℝ :=
  logCellProfile ((bulk.map (fun a => Real.log (value a : ℝ))).sum - cb) *
    logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd)

noncomputable def movingBulkLeafLogWeight {σ : Type*} (value : σ → ℕ)
    (tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    {n : ℕ} (T : MovingSlotData σ n) : ℝ :=
  movingBulkListLogWeight value outside cb cd
    (T.regularSlots.filter (fun a => decide (tier a = k)))

noncomputable def movingBulkTreeLogWeight {σ : Type*} (value : σ → ℕ)
    (tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ
  | _, T@(.leaf _ _) => movingBulkLeafLogWeight value tier k outside cb cd T
  | _, .node _ _ _ _ left right =>
      movingBulkTreeLogWeight value tier k outside cb cd left *
        movingBulkTreeLogWeight value tier k outside cb cd right

theorem movingBulkListLogWeight_bounds {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (cb cd : ℝ) (bulk : List σ) :
    0 ≤ movingBulkListLogWeight value outside cb cd bulk ∧
      movingBulkListLogWeight value outside cb cd bulk ≤ 1 := by
  refine ⟨mul_nonneg (logCellProfile_nonneg _) (logCellProfile_nonneg _), ?_⟩
  exact (mul_le_mul (logCellProfile_le_one _) (logCellProfile_le_one _)
    (logCellProfile_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem movingBulkTreeLogWeight_bounds {σ : Type*} (value : σ → ℕ)
    (tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    {n : ℕ} (T : MovingSlotData σ n) :
    0 ≤ movingBulkTreeLogWeight value tier k outside cb cd T ∧
      movingBulkTreeLogWeight value tier k outside cb cd T ≤ 1 := by
  induction T with
  | leaf => exact movingBulkListLogWeight_bounds value outside cb cd _
  | node s CL CR U left right ihL ihR =>
    exact ⟨mul_nonneg ihL.1 ihR.1,
      (mul_le_mul ihL.2 ihR.2 ihR.1 zero_le_one).trans_eq (one_mul 1)⟩

/-- Real logarithmic weights survive all right-branch conjugations and
factor out as their literal product over the terminal bulk groups. -/
theorem movingDataWeight_bulk_log {σ : Type*} (value : σ → ℕ) (tier : σ → ℕ)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) :
    movingDataWeight (fun T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F T s) E T =
      (movingBulkTreeLogWeight value tier k outside cb cd T : ℂ) * movingDataWeight F E T := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [movingDataWeight, movingBulkTreeLogWeight, ihL, ihR, Complex.ofReal_mul,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    ring

/-- The selected tier is exactly the original bulk. Restored compensation
slots have smaller tiers and cannot enter either logarithmic cutoff. -/
theorem movingBulkTreeLogWeight_sample {σ : Type*} (value : σ → ℕ) (tier : σ → ℕ)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (hn : n ≤ k)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k)
    (ha : a.Levels tier) :
    movingBulkTreeLogWeight value tier k outside cb cd (buildMovingSlotData n t small bulk a) =
      treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) := by
  induction a with
  | leaf =>
    have hs : (small.filter (fun i => decide (tier i = k))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro i hi
      simp [hsmall i hi]
    have hb : (bulk.filter (fun i => decide (tier i = k))) = bulk := by
      apply List.filter_eq_self.mpr
      intro i hi
      simp [hbulk i hi]
    simp only [buildMovingSlotData, movingBulkTreeLogWeight, movingBulkLeafLogWeight,
      MovingSlotData.regularSlots, flattenMovingSlots, List.filter_append, hs, hb, List.nil_append,
      treeLeafMap, treeLeafProduct]
  | @node n u left right ihL ihR =>
    have happ (b c : TreeLeafTuple (List σ) n)
        (hb : ∀ i ∈ flattenMovingSlots n b, tier i ≠ k)
        (hc : ∀ i ∈ flattenMovingSlots n c, tier i ≠ k) :
        ∀ i ∈ flattenMovingSlots n (appendMovingSlotLeaves n b c), tier i ≠ k := by
      intro i hi
      have hi' := (flattenMovingSlots_append_perm n b c).mem_iff.mp hi
      exact (List.mem_append.mp hi').elim (hb i) (hc i)
    have hu : ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n u), tier i ≠ k := by
      intro i hi
      rw [ha.1 i hi]
      omega
    simp only [buildMovingSlotData, movingBulkTreeLogWeight, treeLeafMap, treeLeafProduct]
    rw [ihL _ _ _ (by omega) (happ _ _ hu (fun i hi => hsmall i (List.mem_append_left _ hi)))
      (fun i hi => hbulk i (List.mem_append_left _ hi)) ha.2.1,
      ihR _ _ _ (by omega) (happ _ _ hu (fun i hi => hsmall i (List.mem_append_right _ hi)))
      (fun i hi => hbulk i (List.mem_append_right _ hi)) ha.2.2]

end Ostmann

end OAI
