import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336AdditiveD139

theorem binary_cylinder_isClosed {I : Type u_1} {s : Set (I → Bool)}
    (hs : s ∈ measurableCylinders (fun _ : I => Bool)) : IsClosed s := by
  obtain ⟨S, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact (isClosed_discrete t).preimage S.continuous_restrict

theorem binary_cylinders_eventually_empty {I : Type u_2} {s : ℕ → Set (I → Bool)}
    (hs : ∀ n, s n ∈ measurableCylinders (fun _ : I => Bool))
    (hanti : Antitone s) (hempty : (⋂ n, s n) = ∅) :
    ∃ n, s n = ∅ := by
  by_contra h
  push Not at h
  have hn : ∀ n, (s n).Nonempty := h
  have hc : ∀ n, IsClosed (s n) := fun n => binary_cylinder_isClosed (hs n)
  have hi := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
    (fun n => hanti (Nat.le_succ n)) hn (hc 0).isCompact hc
  rw [hempty] at hi
  exact Set.not_nonempty_empty hi

theorem binary_projective_exists {I : Type u_3}
    (P : (S : Finset I) → Measure (S → Bool))
    [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => Bool) P) :
    ∃ μ : ProbabilityMeasure (I → Bool),
      IsProjectiveLimit (α := fun _ : I => Bool) (μ : Measure (I → Bool)) P := by
  let m := projectiveFamilyContent hP
  have htend : ∀ {s : ℕ → Set (I → Bool)},
      (∀ n, s n ∈ measurableCylinders (fun _ : I => Bool)) →
      Antitone s → (⋂ n, s n) = ∅ →
      Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
    intro s hs hanti hempty
    obtain ⟨N, hN⟩ := binary_cylinders_eventually_empty hs hanti hempty
    have heq : (fun n => m (s n)) =ᶠ[atTop] fun _ => 0 := by
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hsub := hanti hn
      rw [hN] at hsub
      have hz : s n = ∅ := Set.eq_empty_of_subset_empty hsub
      simp [hz, m]
    exact tendsto_const_nhds.congr' heq.symm
  have hsig : m.IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
      isSetRing_measurableCylinders (fun f hf hfU hdisj => ?_)
    exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders m
      (fun _ _ => projectiveFamilyContent_ne_top hP) @htend hf hfU hdisj
  let μ := m.measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge hsig
  have hlim : IsProjectiveLimit (α := fun _ : I => Bool) μ P := by
    intro S
    ext t ht
    rw [Measure.map_apply (Finset.measurable_restrict S) ht]
    change μ (cylinder S t) = P S t
    dsimp [μ]
    rw [AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders _ _ ht)]
    exact projectiveFamilyContent_cylinder hP ht
  have : IsProbabilityMeasure μ := hlim.isProbabilityMeasure
  exact ⟨⟨μ, inferInstance⟩, hlim⟩

theorem binary_projective_exists_unique {I : Type u_4}
    (P : (S : Finset I) → Measure (S → Bool))
    [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => Bool) P) :
    ∃! μ : ProbabilityMeasure (I → Bool),
      IsProjectiveLimit (α := fun _ : I => Bool) (μ : Measure (I → Bool)) P := by
  obtain ⟨μ, hμ⟩ := binary_projective_exists P hP
  exact ⟨μ, hμ, fun ν hν => Subtype.ext (hν.unique hμ)⟩

end Problem336AdditiveD139

end

end OAI
