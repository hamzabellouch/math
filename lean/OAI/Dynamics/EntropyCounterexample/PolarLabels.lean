import OAI.Dynamics.EntropyCounterexample.OrderedIntervalLabels
import OAI.Dynamics.EntropyCounterexample.CompactLabels

namespace OAI

noncomputable section

namespace Problem340

theorem exists_polar_small_fiber_labels {S X : Type*}
    [PseudoMetricSpace S] [CompactSpace S] [PseudoMetricSpace X]
    (A : ℝ) {p : Set.Icc (0 : ℝ) A × S → X} (hp : Continuous p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H K : ℕ, ∃ b : Set.Icc (0 : ℝ) A → Fin (H + 1), ∃ c : S → Fin K,
      Monotone b ∧ ∀ r s u v, b r = b s → c u = c v →
        dist (p (r, u)) (p (s, v)) < ε := by
  have hu : UniformContinuous p := CompactSpace.uniformContinuous_of_continuous hp
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨H, b, hb, hbdiam⟩ := exists_monotone_interval_labels A hδ
  obtain ⟨K, c, hcdiam⟩ := exists_small_fiber_labels (X := S) hδ
  refine ⟨H, K, b, c, hb, ?_⟩
  intro r s u v hrs huv
  apply hmod
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [Subtype.dist_eq, Real.dist_eq] using hbdiam r s hrs
  · exact hcdiam u v huv

theorem polar_orbits_close_of_labels {α S X : Type*} [PseudoMetricSpace X]
    {H K N : ℕ} {R : α → α} {b : α → Fin H} {c : S → Fin K}
    {p : α × S → X} {ε : ℝ}
    (hsmall : ∀ r s u v, b r = b s → c u = c v →
      dist (p (r, u)) (p (s, v)) < ε)
    {r s : α} {u v : S}
    (hword : (fun j : Fin N => b ((R^[j.val]) r)) =
      (fun j : Fin N => b ((R^[j.val]) s))) (hangle : c u = c v) :
    ∀ j : Fin N, dist (p ((R^[j.val]) r, u)) (p ((R^[j.val]) s, v)) < ε := by
  intro j
  exact hsmall _ _ _ _ (congrFun hword j) hangle

end Problem340

end

end OAI
