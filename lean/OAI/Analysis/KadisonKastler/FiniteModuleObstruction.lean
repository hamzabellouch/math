import OAI.Analysis.KadisonKastler.WeakModuleDefect
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Absence of a module map in a compact family has finitely many uniformly
nonzero coefficient witnesses. -/

namespace KadisonKastler

noncomputable section

open scoped Topology

private theorem finite_sum_norm_pos {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∃ i ∈ s, f i ≠ 0) : 0 < ∑ i ∈ s, ‖f i‖ := by
  obtain ⟨i, hi, hf⟩ := h
  exact (norm_pos_iff.mpr hf).trans_le
    (Finset.single_le_sum (f := fun j => ‖f j‖) (fun j _ => norm_nonneg _) hi)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem compact_finite_module_obstruction {M : VonNeumannAlgebra H} {c : ℝ}
    (K : Set (BoundedWeakAlgebraMap M c)) (hK : IsCompact K) (hne : K.Nonempty)
    (hno : ∀ F ∈ K, ¬ ∀ a b, F.map (a * b) = F.map a * b) :
    ∃ (s : Finset (Algebra M × Algebra M × H × H)) (δ : ℝ),
      0 < δ ∧ ∀ F ∈ K,
        δ ≤ ∑ t ∈ s, ‖weakModuleDefect F t.1 t.2.1 t.2.2.1 t.2.2.2‖ := by
  classical
  let U (t : Algebra M × Algebra M × H × H) : Set (BoundedWeakAlgebraMap M c) :=
    {F | weakModuleDefect F t.1 t.2.1 t.2.2.1 t.2.2.2 ≠ 0}
  have ho (t) : IsOpen (U t) :=
    isOpen_ne.preimage (continuous_weakModuleDefect _ _ _ _)
  have hcov : K ⊆ ⋃ t, U t := by
    intro F hF
    have hn : ¬ ∀ a b ξ η, weakModuleDefect F a b ξ η = 0 := by
      simpa only [← right_module_iff_weakModuleDefect_zero] using hno F hF
    push Not at hn
    obtain ⟨a, b, ξ, η, hh⟩ := hn
    exact Set.mem_iUnion.mpr ⟨(a, b, ξ, η), hh⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U ho hcov
  let q (F : BoundedWeakAlgebraMap M c) :=
    ∑ t ∈ s, ‖weakModuleDefect F t.1 t.2.1 t.2.2.1 t.2.2.2‖
  have hq : Continuous q := by
    apply continuous_finsetSum
    intro t _
    exact (continuous_weakModuleDefect _ _ _ _).norm
  have hpos : ∀ F ∈ K, 0 < q F := by
    intro F hF
    obtain ⟨t, ht, hh⟩ := Set.mem_iUnion₂.mp (hs hF)
    exact finite_sum_norm_pos s _ ⟨t, ht, hh⟩
  obtain ⟨F, hF, hmin⟩ := hK.exists_isMinOn hne hq.continuousOn
  exact ⟨s, q F, hpos F hF, hmin⟩

end

end KadisonKastler

end OAI
