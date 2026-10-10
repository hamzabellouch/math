import OAI.Analysis.MetricEntropy.DirectionSampling
import OAI.Analysis.MetricEntropy.DirectionDeletion
import OAI.Analysis.MetricEntropy.FormZeroCount
import OAI.Analysis.MetricEntropy.FormDimension
import OAI.Analysis.MetricEntropy.DirectionBudget
import OAI.Analysis.MetricEntropy.Parameters

namespace OAI

/-!
# Actual directions surviving deletion

The sample is the full finite product of indexed vectors over `ZMod p`.
The actual symmetric-form count and the zero bound for every repeated-index
tuple feed the disjoint-witness union bound. A finite maximum disjoint family
then produces the surviving set separately for each nonzero form.
-/

noncomputable section

namespace MetricEntropyDuality

/-- The actual finite-field direction construction with an explicit deletion
budget. One sample works for every nonzero form; its surviving subset may
depend on that form. All ordered tuples, including repetitions, are retained. -/
theorem exists_robust_directions_of_budget
    {p r h u : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hh : 0 < h) (hu : 0 < u)
    {θ : ℝ} (hθ : θ < 1)
    (hdel : (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤ θ * (u : ℝ))
    (hp_h : h < p) (hp_size : h ^ 2 * u ^ (2 * h) < p) :
    ∃ t : Fin u → Fin r → ZMod p,
      ∀ F : SymmetricForm (ZMod p) r h, F ≠ 0 →
        ∃ T : Finset (Fin u),
          ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧ T.Nonempty ∧
          ∀ a : Fin h → Fin u, (∀ j, a j ∈ T) →
            SymmetricForm.eval F (fun j => t (a j)) ≠ 0 := by
  classical
  let forms : Finset (SymmetricForm (ZMod p) r h) :=
    Finset.univ.filter (fun F => F ≠ 0)
  have hcard : forms.card ≤ p ^ formDimension r h := by
    calc
      forms.card ≤ Fintype.card (SymmetricForm (ZMod p) r h) :=
        Finset.card_le_univ forms
      _ = p ^ formDimension r h := card_form_coefficients p r h
  have hbound : ∀ F ∈ forms, ∀ a : Fin h → Fin u,
      FiniteProductCounting.prob
        (tupleEvent (fun v => SymmetricForm.eval F v = 0) a) ≤ (h : ℝ) / p := by
    intro F hF a
    have hFne : F ≠ 0 := (Finset.mem_filter.mp hF).2
    exact tupleEvent_form_zero_proportion_le hp_h F hFne a
  have hbudget :
      (p : ℝ) ^ formDimension r h * (u : ℝ) ^ (h * (2 * formDimension r h)) *
        ((h : ℝ) / p) ^ (2 * formDimension r h) < 1 :=
    direction_bad_event_bound_lt_one (formDimension_pos hr) hp_size
  obtain ⟨t, ht⟩ := DirectionSampling.exists_sample_avoiding_of_field_budget
    (u := u) (h := h) (w := 2 * formDimension r h)
    forms (fun F v => SymmetricForm.eval F v = 0)
    p (formDimension r h) hcard hbound hbudget
  refine ⟨t, ?_⟩
  intro F hF
  have hFmem : F ∈ forms := Finset.mem_filter.mpr ⟨Finset.mem_univ F, hF⟩
  have hno : ¬ ∃ L : Fin (2 * formDimension r h) → Fin h → Fin u,
      (∀ i, SymmetricForm.eval F (fun j => t (L i j)) = 0) ∧
        DisjointSupports L := by
    rintro ⟨L, hzero, hdisj⟩
    exact ht F hFmem L hdisj hzero
  obtain ⟨T, hTcard, hTgood⟩ := DirectionDeletion.exists_good_subset
    (fun a : Fin h → Fin u => SymmetricForm.eval F (fun j => t (a j)) = 0)
    hh hno
  have hTcardNat : u - T.card ≤ h * (2 * formDimension r h - 1) := by
    simpa only [Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin] using hTcard
  have hTbound : ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
    calc
      ((Finset.univ \ T).card : ℝ) ≤
          ((h * (2 * formDimension r h - 1) : ℕ) : ℝ) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ T),
          Finset.card_univ, Fintype.card_fin]
        exact_mod_cast hTcardNat
      _ ≤ ((h * (2 * formDimension r h) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left h (Nat.sub_le (2 * formDimension r h) 1)
      _ = (h : ℝ) * (2 * (formDimension r h : ℝ)) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ θ * (u : ℝ) := hdel
  have hTnonempty : T.Nonempty := by
    apply Classical.byContradiction
    intro hTempty
    have hTzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTempty
    have hbad : (u : ℝ) ≤ θ * (u : ℝ) := by simpa [hTzero] using hTbound
    have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
    have hstrict : θ * (u : ℝ) < (u : ℝ) := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hθ huR
    exact (not_le_of_gt hstrict) hbad
  exact ⟨T, hTbound, hTnonempty, hTgood⟩

/-- The ceiling-defined direction count satisfies the
deletion budget. The field size is chosen after `r`, `h`, and `θ`. -/
theorem exists_robust_directions
    {p r h : ℕ} [Fact p.Prime] (hr : 0 < r) (hh : 0 < h)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp_h : h < p)
    (hp_size : h ^ 2 * (directionCount r h θ) ^ (2 * h) < p) :
    ∃ t : Fin (directionCount r h θ) → Fin r → ZMod p,
      ∀ F : SymmetricForm (ZMod p) r h, F ≠ 0 →
        ∃ T : Finset (Fin (directionCount r h θ)),
          ((Finset.univ \ T).card : ℝ) ≤ θ * (directionCount r h θ : ℝ) ∧
            T.Nonempty ∧
          ∀ a : Fin h → Fin (directionCount r h θ), (∀ j, a j ∈ T) →
            SymmetricForm.eval F (fun j => t (a j)) ≠ 0 :=
  exists_robust_directions_of_budget hr hh (directionCount_pos hr hh hθ0)
    hθ1 (directionCount_budget hθ0) hp_h hp_size

end MetricEntropyDuality

end

end OAI
