import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

namespace Yau.Geometry
open Set
open scoped ContDiff
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma compact_local_derivative_power_bound (g : E → F) {U Q : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hQ : IsCompact Q) (hQU : Q ⊆ U) (J : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ Q, ∀ i, 1 ≤ i → i ≤ J →
      ‖iteratedFDeriv ℝ i g x‖ ≤ D^i := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i g) Q := by
    intro x hx
    exact ((hg.contDiffAt (hU.mem_nhds (hQU hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).continuousWithinAt
  have hb (i : Fin (J+1)) : ∃ C : ℝ, ∀ x ∈ Q, ‖iteratedFDeriv ℝ i.val g x‖ ≤ C :=
    hQ.exists_bound_of_continuousOn (hc i.val)
  choose C hC using hb
  let D : ℝ := max 1 (∑ i, |C i|)
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨D,hD,?_⟩
  intro x hx i hi hiJ
  let j : Fin (J+1) := ⟨i,by omega⟩
  have hj : C j ≤ D := (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ ↦ abs_nonneg (C k)) (Finset.mem_univ j)).trans (le_max_right _ _))
  exact (hC j x hx).trans (hj.trans (by simpa using pow_le_pow_right₀ hD hi))

theorem compact_local_composition_derivative_bound (g : E → F) {U Q : Set E}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hQ : IsCompact Q) (hQU : Q ⊆ U) (J : ℕ) :
    ∃ C > 0, ∀ (f : F → G), ContDiff ℝ ∞ f → ∀ eps : ℝ, 0 ≤ eps →
      (∀ y i, i ≤ J → ‖iteratedFDeriv ℝ i f y‖ ≤ eps) →
      ∀ x ∈ Q, ∀ i, i ≤ J → ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ C*eps := by
  obtain ⟨D,hD,hDb⟩ := compact_local_derivative_power_bound g hU hg hQ hQU J
  refine ⟨1+(J.factorial:ℝ)*D^J,by positivity,?_⟩
  intro f hf eps heps hb x hx i hi
  have h := norm_iteratedFDerivWithin_comp_le hf.contDiffOn hg
    (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top)) uniqueDiffOn_univ hU.uniqueDiffOn
    (fun _ _ ↦ mem_univ _) (hQU hx)
    (fun k hk ↦ by simpa only [iteratedFDerivWithin_univ] using hb (g x) k (hk.trans hi))
    (fun k hk hki ↦ by
      rw [iteratedFDerivWithin_of_isOpen k hU (hQU hx)]
      exact hDb x hx k hk (hki.trans hi))
  rw [iteratedFDerivWithin_of_isOpen i hU (hQU hx)] at h
  have hfac : (i.factorial:ℝ) ≤ J.factorial := by exact_mod_cast Nat.factorial_le hi
  have hpow : D^i ≤ D^J := pow_le_pow_right₀ hD hi
  calc
    _ ≤ (i.factorial:ℝ)*eps*D^i := h
    _ ≤ (J.factorial:ℝ)*eps*D^J := by gcongr
    _ ≤ (1+(J.factorial:ℝ)*D^J)*eps := by nlinarith

end
end Yau.Geometry

end OAI
