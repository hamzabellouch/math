import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Extend convergent parameter subsequences to all integer nonlinearity powers. -/

open Filter
namespace DefocusingNLS

noncomputable def radialParameterExtension (s : ℕ → ℕ) (z : ℕ → ℂ) (w : ℂ) (n : ℕ) : ℂ := by
  classical
  exact if h : ∃ i, s i=n then z (Classical.choose h) else w

theorem radialParameterExtension_apply (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ℂ) (w : ℂ) (i : ℕ) : radialParameterExtension s z w (s i)=z i := by
  classical
  rw [radialParameterExtension,dite_eq_left (show ∃ k, s k=s i from ⟨i,rfl⟩)]
  congr 1
  exact hs.injective (Classical.choose_spec (show ∃ k, s k=s i from ⟨i,rfl⟩))

theorem radialParameterExtension_tendsto (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ℂ) (w : ℂ) (hz : Tendsto z atTop (nhds w)) :
    Tendsto (radialParameterExtension s z w) atTop (nhds w) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp hz ε hε
  refine ⟨s K,?_⟩
  intro n hn
  by_cases he : ∃ i, s i=n
  · rw [radialParameterExtension,dite_eq_left he]
    have hi : K ≤ Classical.choose he := hs.le_iff_le.mp (by
      rw [Classical.choose_spec he]
      exact hn)
    exact hK _ hi
  · simpa only [radialParameterExtension,dite_eq_right he,dist_self] using hε

end DefocusingNLS

end OAI
