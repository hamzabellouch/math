import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevUniqueness
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # Uniqueness throughout a common open time interval -/

open Filter Topology Set Metric

namespace DefocusingNLS

/-- On an interval where both curves are bounded, one initial value determines the solution. -/
theorem sobolevInteractionSolution_unique_of_bounded
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v w : ℝ → FourierL2)
    (a b t₀ R : ℝ) (hR : 0 ≤ R) (ht₀ : t₀ ∈ Ioo a b)
    (hv : ∀ t ∈ Ioo a b, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t)
    (hvb : ∀ t ∈ Ioo a b, ‖v t‖ ≤ R) (hwb : ∀ t ∈ Ioo a b, ‖w t‖ ≤ R)
    (heq : v t₀ = w t₀) : EqOn v w (Ioo a b) := by
  obtain ⟨A, K, hA, hK, hbound, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m R hR
  apply ODE_solution_unique_of_mem_Ioo
    (v := schrodingerInteractionField k hk m) (s := fun _ => closedBall 0 R)
    (K := ⟨K, hK⟩) ?_ ht₀ ?_ ?_ heq
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro f hf g hg
    rw [dist_eq_norm, dist_eq_norm]
    change ‖schrodingerInteractionField k hk m t f - schrodingerInteractionField k hk m t g‖ ≤
      K * ‖f - g‖
    exact hlip t f g (by simpa using hf) (by simpa using hg)
  · intro t ht
    exact ⟨hv t ht, by simpa using hvb t ht⟩
  · intro t ht
    exact ⟨hw t ht, by simpa using hwb t ht⟩

/-- Two classical Sobolev interaction solutions agree on their entire common interval. -/
theorem sobolevInteractionSolution_unique_on_interval
    (k : ℝ) (hk : 6 < k) (m : ℕ) (v w : ℝ → FourierL2)
    (a b t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b)
    (hv : ∀ t ∈ Ioo a b, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t)
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t)
    (heq : v t₀ = w t₀) : EqOn v w (Ioo a b) := by
  intro t ht
  let a' := (a + min t₀ t) / 2
  let b' := (b + max t₀ t) / 2
  have hamin : a < min t₀ t := lt_min ht₀.1 ht.1
  have hmaxb : max t₀ t < b := max_lt ht₀.2 ht.2
  have ha' : a < a' := by dsimp [a']; linarith
  have hb' : b' < b := by dsimp [b']; linarith
  have h₀ : t₀ ∈ Ioo a' b' := by
    have hm := min_le_left t₀ t
    have hM := le_max_left t₀ t
    dsimp [a', b']
    constructor <;> linarith
  have ht' : t ∈ Ioo a' b' := by
    have hm := min_le_right t₀ t
    have hM := le_max_right t₀ t
    dsimp [a', b']
    constructor <;> linarith
  have hsub : Icc a' b' ⊆ Ioo a b := by
    intro s hs
    exact ⟨lt_of_lt_of_le ha' hs.1, lt_of_le_of_lt hs.2 hb'⟩
  have hvc : ContinuousOn v (Icc a' b') := fun s hs =>
    (hv s (hsub hs)).continuousAt.continuousWithinAt
  have hwc : ContinuousOn w (Icc a' b') := fun s hs =>
    (hw s (hsub hs)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hwc
  let R := max (max C D) 0
  have hR : 0 ≤ R := le_max_right _ _
  have hsmall : Ioo a' b' ⊆ Ioo a b := Ioo_subset_Icc_self.trans hsub
  have he := sobolevInteractionSolution_unique_of_bounded k hk m v w a' b' t₀ R hR h₀
    (fun s hs => hv s (hsmall hs)) (fun s hs => hw s (hsmall hs))
    (fun s hs => (hC s (Ioo_subset_Icc_self hs)).trans
      ((le_max_left C D).trans (le_max_left _ _)))
    (fun s hs => (hD s (Ioo_subset_Icc_self hs)).trans
      ((le_max_right C D).trans (le_max_left _ _))) heq
  exact he ht'

end DefocusingNLS

end OAI
