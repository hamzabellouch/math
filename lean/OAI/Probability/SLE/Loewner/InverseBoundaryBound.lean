import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Hydrodynamic normalization prevents an inverse chart from escaping to
infinity above a bounded set. This is independent of boundary extension. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma inverse_bound_of_hydrodynamic {D : Set ℂ} {g f : ℂ → ℂ} {c : ℂ}
    (hmap : MapsTo f upperHalfPlane D)
    (hinv : ∀ w∈upperHalfPlane, g (f w)=w)
    (hlim : Tendsto (fun z : ℂ => z*(g z-z)) (cocompact ℂ ⊓ 𝓟 D) (𝓝 c))
    (R : ℝ) : ∃ M : ℝ, ∀ w∈upperHalfPlane, ‖w‖≤R → ‖f w‖≤M := by
  have he := Metric.tendsto_nhds.mp hlim 1 zero_lt_one
  rw [eventually_inf_principal,← Metric.cobounded_eq_cocompact] at he
  obtain ⟨N,_,hN⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  refine ⟨max (max N 1) (R+‖c‖+1),fun w hw hR => ?_⟩
  by_cases hz : ‖f w‖ ≤ max N 1
  · exact hz.trans (le_max_left _ _)
  have hz' := lt_of_not_ge hz
  have hzN : N≤‖f w‖ := (le_max_left _ _).trans hz'.le
  have hz1 : 1≤‖f w‖ := (le_max_right _ _).trans hz'.le
  have hsmall := hN hzN (hmap hw)
  have hp : ‖f w‖*‖g (f w)-f w‖≤‖c‖+1 := by
    have htri := norm_le_norm_sub_add (f w*(g (f w)-f w)) c
    rw [norm_mul] at htri
    have hd : ‖f w*(g (f w)-f w)-c‖<1 := by simpa only [dist_eq_norm] using hsmall
    linarith
  have hd : ‖g (f w)-f w‖≤‖c‖+1 :=
    (le_mul_of_one_le_left (norm_nonneg _) hz1).trans hp
  have htri := norm_le_norm_sub_add (f w) (g (f w))
  rw [hinv w hw] at htri hd
  rw [norm_sub_rev w (f w)] at hd
  exact (show ‖f w‖≤R+‖c‖+1 by linarith).trans (le_max_right _ _)

lemma IsCapacityTwoWitness.inverse_bounded_over_ball
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (R : ℝ) :
    ∃ M : ℝ, ∀ w∈upperHalfPlane, ‖w‖≤R → ‖F t w‖≤M :=
  inverse_bound_of_hydrodynamic (hw.2.2.2.2.2.2.1 t)
    (hw.2.2.2.2.2.2.2.2.1 t) (hw.2.2.2.2.2.2.2.2.2.2.2.1 t) R

end SLEExactGauge

end

end OAI
