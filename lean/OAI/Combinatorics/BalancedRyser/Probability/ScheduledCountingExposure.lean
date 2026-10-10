import Mathlib.Order.RelClasses
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionCountingExposure
import OAI.Combinatorics.BalancedRyser.Deletion.UniformDeletionEnumeration
import OAI.Combinatorics.BalancedRyser.Probability.ExposureInterleaving
import OAI.Combinatorics.BalancedRyser.Probability.ExposureScheduleOrder
import OAI.Combinatorics.BalancedRyser.Profiles.MarkedExposureNumerics
import OAI.Combinatorics.BalancedRyser.Profiles.StrictOrderMarkedExposure

namespace OAI

namespace Balanced.ScheduledCountingExposure

universe u

noncomputable section
open scoped Classical BigOperators ENNReal
open ExposureInterleaving CountingExposurePosterior
open UniformDeletionEnumeration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {k m : ℕ}

abbrev DExperiment (F : Type*) [Fintype F] (k : ℕ) :=
  CountingExposurePosterior.Experiment (G := Direction F) (ι := Fin k) (α := F)

abbrev Sample (F : Type*) [Fintype F] (k : ℕ) :=
  DExperiment F k × Equiv.Perm (Line F)

abbrev Steps (F : Type*) [Fintype F] (k m : ℕ) :=
  Step (k * (Fintype.card F + 1)) m

def pastD (γ : ℝ) (s : Steps F k m) : Finset (Direction F × Fin k) :=
  (previousD γ s).map timeToToken.toEmbedding

def pastC (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m) : Finset (Line F) :=
  (previousC γ s).map c

def uncovered (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) : Finset (Point F) :=
  uncoveredBy (DeletionCountingExposure.exposedLines (pastD γ s) ω.1 ∪
    (pastC c γ s).map ω.2.toEmbedding)

def target (c : Fin m ↪ Line F) : Steps F k m → Sample F k → Line F
  | Sum.inl i, ω => nextLine ω.1 (timeToToken i)
  | Sum.inr i, ω => ω.2 (c i)

def Mark (c : Fin m ↪ Line F) (γ η ε : ℝ) (s : Steps F k m)
    (ω : Sample F k) : Prop :=
  η < parameter γ s ∧ CoverCountingExposure.Marked (uncovered c γ s ω) ε (target c s ω)

def markCount (c : Fin m ↪ Line F) (γ η ε : ℝ) (ω : Sample F k) : ℕ :=
  (Finset.univ.filter (fun s => Mark c γ η ε s ω)).card

def arrayUncovered (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ : ℝ) (s : Steps F k m) : Finset (Point F) :=
  uncoveredBy ((previousD γ s).image d ∪ (previousC γ s).image c)

def arrayMark (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ η ε : ℝ) (s : Steps F k m) : Prop :=
  η < parameter γ s ∧ CoverCountingExposure.Marked (arrayUncovered d c γ s) ε
    (Sum.elim d c s)

def arrayMarkCount (d : Fin (k * (Fintype.card F + 1)) → Line F)
    (c : Fin m → Line F) (γ η ε : ℝ) : ℕ :=
  (Finset.univ.filter (arrayMark d c γ η ε)).card

theorem mark_eq_arrayMark (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (s : Steps F k m) (ω : Sample F k) :
    Mark c γ η ε s ω = arrayMark
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ η ε s := by
  have hu : uncovered c γ s ω = arrayUncovered
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ s := by
    simp [uncovered, arrayUncovered, DeletionCountingExposure.exposedLines,
      pastD, pastC, Finset.map_eq_image, Finset.image_image, Function.comp_def]
  cases s <;> simp only [Mark, arrayMark, hu, target, Sum.elim_inl, Sum.elim_inr]

theorem markCount_eq_arrayMarkCount (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (ω : Sample F k) :
    markCount c γ η ε ω = arrayMarkCount
      (fun i => nextLine ω.1 (timeToToken i)) (fun i => ω.2 (c i)) γ η ε := by
  simp only [markCount, arrayMarkCount, mark_eq_arrayMark]

omit [Field F] [DecidableEq F] in
theorem pastD_mono {γ : ℝ} (hγ : 0 < γ) {s t : Steps F k m}
    (hst : Before γ s t) : pastD γ s ⊆ pastD γ t := by
  apply Finset.map_subset_map.mpr
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

omit [Field F] [DecidableEq F] in
theorem pastC_mono (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    {s t : Steps F k m} (hst : Before γ s t) : pastC c γ s ⊆ pastC c γ t := by
  apply Finset.map_subset_map.mpr
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

omit [Field F] [DecidableEq F] in
theorem deletion_position_mem {γ : ℝ} {i : Fin (k * (Fintype.card F + 1))}
    {s : Steps F k m} (h : Before γ (Sum.inl i) s) :
    timeToToken i ∈ pastD γ s :=
  Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

omit [Field F] [DecidableEq F] in
theorem cover_position_mem (c : Fin m ↪ Line F) {γ : ℝ} {i : Fin m}
    {s : Steps F k m} (h : Before γ (Sum.inr i) s) : c i ∈ pastC c γ s :=
  Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

omit [Field F] [DecidableEq F] in
theorem deletion_position_not_mem (γ : ℝ) (i : Fin (k * (Fintype.card F + 1))) :
    timeToToken i ∉ pastD γ (Sum.inl i : Steps F k m) := by
  simpa only [pastD, Finset.mem_map_equiv, Equiv.symm_apply_apply] using currentD_not_previousD (m := m) γ i

omit [Field F] [DecidableEq F] in
theorem cover_position_not_mem (c : Fin m ↪ Line F) (γ : ℝ) (i : Fin m) :
    c i ∉ pastC c γ (Sum.inr i : Steps F k m) := by
  simpa only [pastC, Finset.mem_map, c.injective.eq_iff, exists_eq_right] using currentC_not_previousC
    (n := k * (Fintype.card F + 1)) γ i

theorem uncovered_eq_D (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) :
    uncovered c γ s ω = DeletionCountingExposure.pastUncovered
      ((pastC c γ s).map ω.2.toEmbedding) (pastD γ s) ω.1 := rfl

theorem uncovered_eq_C (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m)
    (ω : Sample F k) :
    uncovered c γ s ω = CoverCountingExposure.pastUncovered
      (DeletionCountingExposure.exposedLines (pastD γ s) ω.1) (pastC c γ s) ω.2 := rfl

theorem mark_iff_D_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) {s t : Steps F k m} (hst : Before γ s t)
    (σ : Equiv.Perm (Line F)) (ω τ : DExperiment F k)
    (h : ω ∈ countingHistory (pastD γ t) τ.1 τ.2) :
    Mark c γ η ε s (ω, σ) ↔ Mark c γ η ε s (τ, σ) := by
  unfold Mark
  apply and_congr_right
  intro _
  rw [uncovered_eq_D, uncovered_eq_D]
  cases s with
  | inl i =>
    exact DeletionCountingExposure.earlier_deletion_mark_iff _ _ _
      (pastD_mono hγ hst) _ (deletion_position_mem hst) ω τ h ε
  | inr i =>
    exact DeletionCountingExposure.earlier_cover_mark_iff _ _ _
      (pastD_mono hγ hst) _ ω τ h ε

theorem mark_iff_C_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) {s t : Steps F k m} (hst : Before γ s t)
    (ω : DExperiment F k) (σ τ : Equiv.Perm (Line F))
    (h : σ ∈ PermutationHistoryLaw.histories (pastC c γ t) τ) :
    Mark c γ η ε s (ω, σ) ↔ Mark c γ η ε s (ω, τ) := by
  unfold Mark
  apply and_congr_right
  intro _
  rw [uncovered_eq_C, uncovered_eq_C]
  cases s with
  | inl i =>
    exact CoverCountingExposure.earlier_deletion_mark_iff _ _ _
      (pastC_mono c hγ hst) _ σ τ h ε
  | inr i =>
    exact CoverCountingExposure.earlier_cover_mark_iff _ _ _
      (pastC_mono c hγ hst) _ (cover_position_mem c hst) σ τ h ε

def Cylinder (c : Fin m ↪ Line F) (γ η ε : ℝ)
    (t : Finset (Steps F k m)) (ω : Sample F k) : Prop :=
  ∀ s ∈ t, Mark c γ η ε s ω

theorem cylinder_iff_D_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) (σ : Equiv.Perm (Line F))
    (ω τ : DExperiment F k) (h : ω ∈ countingHistory (pastD γ s) τ.1 τ.2) :
    Cylinder c γ η ε t (ω, σ) ↔ Cylinder c γ η ε t (τ, σ) := by
  constructor
  · intro ha u hu
    exact (mark_iff_D_history c hγ η ε (ht u hu) σ ω τ h).mp (ha u hu)
  · intro ha u hu
    exact (mark_iff_D_history c hγ η ε (ht u hu) σ ω τ h).mpr (ha u hu)

theorem cylinder_iff_C_history (c : Fin m ↪ Line F) {γ : ℝ} (hγ : 0 < γ)
    (η ε : ℝ) (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) (ω : DExperiment F k)
    (σ τ : Equiv.Perm (Line F))
    (h : σ ∈ PermutationHistoryLaw.histories (pastC c γ s) τ) :
    Cylinder c γ η ε t (ω, σ) ↔ Cylinder c γ η ε t (ω, τ) := by
  constructor
  · intro ha u hu
    exact (mark_iff_C_history c hγ η ε (ht u hu) ω σ τ h).mp (ha u hu)
  · intro ha u hu
    exact (mark_iff_C_history c hγ η ε (ht u hu) ω σ τ h).mpr (ha u hu)

omit [Field F] [DecidableEq F] in
theorem activeD_remaining (γ η : ℝ) (i : Fin (k * (Fintype.card F + 1)))
    (hactive : η < parameter γ (Sum.inl i : Steps F k m)) :
    η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ((k * (Fintype.card F + 1) - (pastD γ (Sum.inl i : Steps F k m)).card : ℕ) : ℝ) := by
  have hc := previousD_add_remainingD γ (Sum.inl i : Steps F k m)
  rw [remainingD_at_D] at hc
  have he : k * (Fintype.card F + 1) -
      (pastD γ (Sum.inl i : Steps F k m)).card = i.val + 1 := by
    simp only [pastD, Finset.card_map]
    omega
  rw [he]
  have hn : (0 : ℝ) < (k * (Fintype.card F + 1) : ℕ) := by
    exact_mod_cast Nat.zero_lt_of_lt i.isLt
  change η < (i.val + 1 : ℝ) / (k * (Fintype.card F + 1) : ℕ) at hactive
  have hb := (lt_div_iff₀ hn).mp hactive
  push_cast at hb ⊢
  nlinarith

omit [Field F] [DecidableEq F] in
theorem pastC_card_le (c : Fin m ↪ Line F) (γ : ℝ) (s : Steps F k m) :
    (pastC c γ s).card ≤ m := by
  simp only [pastC, Finset.card_map]
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin m)

omit [Field F] in
theorem expect_sample (g : Sample F k → ℝ) :
    (𝔼 ω : Sample F k, g ω) =
      𝔼 ω : DExperiment F k, 𝔼 σ : Equiv.Perm (Line F), g (ω, σ) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

omit [Field F] in
theorem expect_sample_swap (g : Sample F k → ℝ) :
    (𝔼 ω : Sample F k, g ω) =
      𝔼 σ : Equiv.Perm (Line F), 𝔼 ω : DExperiment F k, g (ω, σ) := by
  rw [expect_sample, Finset.expect_comm]

theorem step_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) :
    (𝔼 ω : Sample F k, if Mark c γ η ε s ω ∧ Cylinder c γ η ε t ω
      then (1 : ℝ) else 0) ≤
      ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (𝔼 ω : Sample F k, if Cylinder c γ η ε t ω then (1 : ℝ) else 0) := by
  by_cases hactive : η < parameter γ s
  · cases s with
    | inl i =>
      rw [expect_sample_swap, expect_sample_swap]
      have h := DeletionCountingExposure.independent_outer_past_event_and_actual_mark_le
        (fun σ : Equiv.Perm (Line F) => (pastC c γ (Sum.inl i)).map σ.toEmbedding)
        (pastD γ (Sum.inl i)) (timeToToken i) (deletion_position_not_mem γ i)
        (fun σ ω => Cylinder c γ η ε t (ω, σ))
        (fun σ ω τ h => cylinder_iff_D_history c hγ η ε (Sum.inl i) t ht σ ω τ h)
        ε η hε hη hk hqk (activeD_remaining γ η i hactive)
      simpa only [Mark, hactive, true_and, uncovered_eq_D, target, and_comm] using h
    | inr i =>
      rw [expect_sample, expect_sample, Finset.mul_expect]
      apply Finset.expect_le_expect
      intro ω _
      have h := CoverCountingExposure.past_event_and_actual_mark_le
        (DeletionCountingExposure.exposedLines (pastD γ (Sum.inr i)) ω)
        (pastC c γ (Sum.inr i)) ((pastC_card_le c γ _).trans hm)
        (c i) (cover_position_not_mem c γ i)
        (fun σ => Cylinder c γ η ε t (ω, σ))
        (fun σ τ h => cylinder_iff_C_history c hγ η ε (Sum.inr i) t ht ω σ τ h) hε
      have hf : (1 : ℝ) / (4 * ε ^ 2 * Fintype.card F) ≤
          (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (le_div_iff₀ hη).mpr (by linarith)
      have hp : 0 ≤ (𝔼 σ : Equiv.Perm (Line F),
          if Cylinder c γ η ε t (ω, σ) then (1 : ℝ) else 0) := by
        apply Finset.expect_nonneg
        intro σ _
        split_ifs <;> norm_num
      have h' := h.trans (mul_le_mul_of_nonneg_right hf hp)
      simpa only [Mark, hactive, true_and, uncovered_eq_C, target, and_comm] using h'
  · have hzero : (𝔼 ω : Sample F k,
        if Mark c γ η ε s ω ∧ Cylinder c γ η ε t ω then (1 : ℝ) else 0) = 0 := by
      simp [Mark, hactive]
    rw [hzero]
    apply mul_nonneg (by positivity)
    apply Finset.expect_nonneg
    intro ω _
    split_ifs <;> norm_num

omit [Field F] [DecidableEq F] in
theorem sampleNonempty (hk : k ≤ Fintype.card F) : Nonempty (Sample F k) :=
  ⟨((Equiv.refl _, canonicalOffsets hk), Equiv.refl _)⟩

section Measure
variable [Nonempty (Sample F k)] [MeasurableSpace (Sample F k)]
  [MeasurableSingletonClass (Sample F k)]

theorem step_measure_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (s : Steps F k m) (t : Finset (Steps F k m))
    (ht : ∀ u ∈ t, Before γ u s) :
    (PMF.uniformOfFintype (Sample F k)).toMeasure
        ({ω | Mark c γ η ε s ω} ∩ (⋂ u ∈ t, {ω | Mark c γ η ε u ω})) ≤
      ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) *
        (PMF.uniformOfFintype (Sample F k)).toMeasure
          (⋂ u ∈ t, {ω | Mark c γ η ε u ω}) := by
  have hc : (⋂ u ∈ t, {ω | Mark c γ η ε u ω}) =
      {ω | Cylinder c γ η ε t ω} := by
    ext ω
    simp [Cylinder]
  rw [hc]
  apply (ENNReal.toReal_le_toReal
    (MeasureTheory.measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h := step_expect_le c hγ hη hη1 hε hk hqk hm s t ht
  rw [← PermutationHistoryLaw.uniform_measureReal_eq_expect,
    ← PermutationHistoryLaw.uniform_measureReal_eq_expect] at h
  exact h

theorem markCount_tail_measure_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (r : ℕ) :
    (PMF.uniformOfFintype (Sample F k)).toMeasure
        {ω | r ≤ markCount c γ η ε ω} ≤
      (2 : ℝ≥0∞) ^ (k * (Fintype.card F + 1) + m) *
        ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) ^ r := by
  let : IsStrictTotalOrder (Steps F k m) (Before γ) := beforeStrictTotalOrder hγ
  have h := MarkedExposure.tail_le_two_pow_mul_of_strict_order
    (PMF.uniformOfFintype (Sample F k)).toMeasure (Before γ)
    (fun s : Steps F k m => {ω | Mark c γ η ε s ω}) Finset.univ r
    (ENNReal.ofReal ((2 / η) / (4 * ε ^ 2 * Fintype.card F))) (by
      intro s _ t _ ht
      exact step_measure_le c hγ hη hη1 hε hk hqk hm s t ht)
  simpa only [MarkedExposure.atLeast, markCount, Finset.card_univ,
    Steps, Step, Fintype.card_sum, Fintype.card_fin, Set.mem_ofPred_eq] using h

end Measure

theorem markCount_tail_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (r : ℕ) :
    (𝔼 ω : Sample F k, if r ≤ markCount c γ η ε ω then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (k * (Fintype.card F + 1) + m) *
        ((2 / η) / (4 * ε ^ 2 * Fintype.card F)) ^ r := by
  let : Nonempty (Sample F k) := sampleNonempty (by omega)
  let : MeasurableSpace (Sample F k) := ⊤
  have h := markCount_tail_measure_le c hγ hη hη1 hε hk hqk hm r
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (show 0 ≤ (2 / η) / (4 * ε ^ 2 * Fintype.card F) by positivity)] at hr
  rw [← PermutationHistoryLaw.uniform_measureReal_eq_expect]
  exact hr

theorem rare_mark_expect_le (c : Fin m ↪ Line F) {γ η ε : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (ξ : ℝ) (hBq : max 1 ((2 / η) / (4 * ε ^ 2)) ≤ (Fintype.card F : ℝ)) :
    (𝔼 ω : Sample F k,
      if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
        then (1 : ℝ) else 0) ≤
      Real.exp (MarkedExposureNumerics.exponentialCost (2 * k + 1)
        ((2 / η) / (4 * ε ^ 2)) ξ * Fintype.card F -
          ξ * Fintype.card F * Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have ht := markCount_tail_expect_le c hγ hη hη1 hε hk hqk hm
    ⌈(m : ℝ) + ξ * Fintype.card F⌉₊
  have hn := MarkedExposureNumerics.two_pow_mul_pow_le (Fintype.card F) m
    (k * (Fintype.card F + 1) + m) ⌈(m : ℝ) + ξ * Fintype.card F⌉₊
    (2 * k + 1) ((2 / η) / (4 * ε ^ 2)) ξ hq (by positivity) hBq hm
    (MarkedExposureNumerics.exposure_length_le k (Fintype.card F) m hq hm)
    (Nat.le_ceil _)
  rw [div_div] at hn
  simpa only [Nat.ceil_le] using ht.trans hn

theorem markCount_eq_zero_of_one_le_cutoff (c : Fin m ↪ Line F)
    {γ η : ℝ} (hγ : 0 < γ) (hη : 1 ≤ η) (ε : ℝ) (ω : Sample F k) :
    markCount c γ η ε ω = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro s _ hs
  exact (not_lt_of_ge ((parameter_le_one hγ s).trans hη)) hs.1

theorem rare_mark_expect_le_all_cutoffs (c : Fin m ↪ Line F) {γ η ε ξ : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F) (hm : m ≤ Fintype.card F)
    (hBq : max 1 ((2 / η) / (4 * ε ^ 2)) ≤ (Fintype.card F : ℝ)) :
    (𝔼 ω : Sample F k,
      if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
        then (1 : ℝ) else 0) ≤
      Real.exp (MarkedExposureNumerics.exponentialCost (2 * k + 1)
        ((2 / η) / (4 * ε ^ 2)) ξ * Fintype.card F -
          ξ * Fintype.card F * Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  by_cases hη1 : η ≤ 1
  · exact rare_mark_expect_le c hγ hη hη1 hε hk hqk hm ξ hBq
  · have hη' : 1 ≤ η := (lt_of_not_ge hη1).le
    have hpos : (0 : ℝ) < (m : ℝ) + ξ * Fintype.card F := by positivity
    simp only [markCount_eq_zero_of_one_le_cutoff c hγ hη', Nat.cast_zero,
      not_le_of_gt hpos, ite_false, Finset.expect_const_zero]
    positivity

theorem uniform_rare_mark_bound (k : ℕ) (hk : 0 < k) (γ η ε ξ : ℝ)
    (hγ : 0 < γ) (hη : 0 < η) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ L : ℝ, ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (m : ℕ) (c : Fin m ↪ Line F), N ≤ Fintype.card F → m ≤ Fintype.card F →
        (𝔼 ω : Sample F k,
          if (m : ℝ) + ξ * Fintype.card F ≤ (markCount c γ η ε ω : ℝ)
            then (1 : ℝ) else 0) ≤
          Real.exp (L * Fintype.card F - ξ * Fintype.card F *
            Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m := by
  let B : ℝ := (2 / η) / (4 * ε ^ 2)
  refine ⟨MarkedExposureNumerics.exponentialCost (2 * k + 1) B ξ,
    max (2 * k) ⌈max 1 B⌉₊, ?_⟩
  intro F _ _ _ m c hN hm
  have hqk : 2 * k ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hceil : ⌈max 1 B⌉₊ ≤ Fintype.card F := (le_max_right _ _).trans hN
  have hBq : max 1 B ≤ (Fintype.card F : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  exact rare_mark_expect_le_all_cutoffs c hγ hη hε hξ hk hqk hm hBq

end
end Balanced.ScheduledCountingExposure

end OAI
