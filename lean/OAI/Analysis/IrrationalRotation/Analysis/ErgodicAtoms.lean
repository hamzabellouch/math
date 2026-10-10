import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Conservative

namespace OAI

open Set Filter Function MeasureTheory

namespace Invariant233.ErgodicAtoms

variable {X : Type*} [m : MeasurableSpace X] {μ : Measure X}

theorem exists_positive_period_of_disjoint_or_equal
    [IsFiniteMeasure μ] {T : X → X} (hT : MeasurePreserving T μ μ)
    {s : Set X} (hs : MeasurableSet s) (hpos : μ s ≠ 0)
    (horbit : ∀ n : ℕ, 0 < n →
      μ (s ∩ T^[n] ⁻¹' s) = 0 ∨ T^[n] ⁻¹' s =ᵐ[μ] s) :
    ∃ n : ℕ, 0 < n ∧ T^[n] ⁻¹' s =ᵐ[μ] s := by
  obtain ⟨n, hn, hinter⟩ :=
    hT.conservative.exists_gt_measure_inter_ne_zero hs.nullMeasurableSet hpos 0
  exact ⟨n, hn, (horbit n hn).resolve_left hinter⟩

theorem ae_eq_univ_of_positive_period
    {T : X → X} (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    {s : Set X} (hs : MeasurableSet s) (hpos : μ s ≠ 0)
    (hperiod : ∃ n : ℕ, 0 < n ∧ T^[n] ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] Set.univ := by
  obtain ⟨n, hn, hperiod⟩ := hperiod
  rcases (hT n hn).quasiErgodic.ae_empty_or_univ₀ hs.nullMeasurableSet hperiod with h | h
  · exact False.elim (hpos (by simpa using measure_congr h))
  · exact h

theorem ae_eq_univ_of_disjoint_or_equal
    [IsFiniteMeasure μ] {T : X → X}
    (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    {s : Set X} (hs : MeasurableSet s) (hpos : μ s ≠ 0)
    (horbit : ∀ n : ℕ, 0 < n →
      μ (s ∩ T^[n] ⁻¹' s) = 0 ∨ T^[n] ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] Set.univ := by
  apply ae_eq_univ_of_positive_period hT hs hpos
  have hT1 : MeasurePreserving T μ μ := by
    simpa using (hT 1 (by decide)).toMeasurePreserving
  exact exists_positive_period_of_disjoint_or_equal hT1 hs hpos horbit

theorem ae_eq_univ_of_measurable_atom
    [IsFiniteMeasure μ] {T : X → X}
    (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    (m₀ : MeasurableSpace X) (hm₀ : m₀ ≤ m)
    (hT₀ : @Measurable X X m₀ m₀ T)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hpos : μ s ≠ 0)
    (hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0) :
    s =ᵐ[μ] Set.univ := by
  let : MeasurableSpace X := m
  have hs : MeasurableSet s := hm₀ s hs₀
  have hT1 : MeasurePreserving T μ μ := by
    simpa using (hT 1 (by decide)).toMeasurePreserving
  obtain ⟨n, hn, hinter⟩ :=
    hT1.conservative.exists_gt_measure_inter_ne_zero hs.nullMeasurableSet hpos 0
  have hint₀ : @MeasurableSet X m₀ (s ∩ T^[n] ⁻¹' s) :=
    hs₀.inter ((hT₀.iterate n) hs₀)
  have hnull : μ (s \ (s ∩ T^[n] ⁻¹' s)) = 0 :=
    (hatom _ hint₀ inter_subset_left).resolve_left hinter
  have hle : s ≤ᵐ[μ] T^[n] ⁻¹' s := by
    apply ae_le_set.mpr
    simpa only [inter_comm s, sdiff_inter_self_eq_sdiff] using hnull
  rcases (hT n hn).ae_empty_or_univ_of_ae_le_preimage hs.nullMeasurableSet hle with h | h
  · exact False.elim (hpos (by simpa using measure_congr h))
  · exact h

theorem ae_empty_or_univ_of_conull_atom
    (m₀ : MeasurableSpace X)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hfull : s =ᵐ[μ] Set.univ)
    (hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0)
    {t : Set X} (ht₀ : @MeasurableSet X m₀ t) :
    t =ᵐ[μ] (∅ : Set X) ∨ t =ᵐ[μ] Set.univ := by
  let : MeasurableSpace X := m
  have hinter : (s ∩ t : Set X) =ᵐ[μ] t :=
    inter_ae_eq_right_of_ae_eq_univ hfull
  rcases hatom (s ∩ t) (hs₀.inter ht₀) inter_subset_left with h | h
  · left
    apply ae_eq_empty.mpr
    rwa [measure_congr hinter] at h
  · right
    have hle : s ≤ᵐ[μ] t := by
      apply ae_le_set.mpr
      simpa only [inter_comm s, sdiff_inter_self_eq_sdiff] using h
    exact EventuallyLE.antisymm (subset_univ t).eventuallyLE (hfull.symm.le.trans hle)

theorem exists_nontrivial_measurable_subset
    [IsFiniteMeasure μ] {T : X → X}
    (hT : ∀ n : ℕ, 0 < n → Ergodic T^[n] μ)
    (m₀ : MeasurableSpace X) (hm₀ : m₀ ≤ m)
    (hT₀ : @Measurable X X m₀ m₀ T)
    (hnontrivial : ∃ t : Set X, @MeasurableSet X m₀ t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0)
    {s : Set X} (hs₀ : @MeasurableSet X m₀ s) (hpos : μ s ≠ 0) :
    ∃ t : Set X, @MeasurableSet X m₀ t ∧ t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  let : MeasurableSpace X := m
  by_contra hsplit
  have hatom : ∀ t : Set X, @MeasurableSet X m₀ t → t ⊆ s →
      μ t = 0 ∨ μ (s \ t) = 0 := by
    intro t ht hts
    by_cases hzero : μ t = 0
    · exact Or.inl hzero
    · right
      by_contra hcomp
      exact hsplit ⟨t, ht, hts, hzero, hcomp⟩
  have hfull := ae_eq_univ_of_measurable_atom hT m₀ hm₀ hT₀ hs₀ hpos hatom
  obtain ⟨t, ht, htpos, htcomp⟩ := hnontrivial
  rcases ae_empty_or_univ_of_conull_atom m₀ hs₀ hfull hatom ht with h | h
  · exact htpos (ae_eq_empty.mp h)
  · exact htcomp (ae_eq_univ.mp h)

end Invariant233.ErgodicAtoms

end OAI
