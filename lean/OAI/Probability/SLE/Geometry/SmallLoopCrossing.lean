import OAI.Probability.SLE.Geometry.SingleCrossingObstruction

namespace OAI

/-! A loop contained in a ball cannot have exactly one locally invertible
crossing with a path whose two endpoints lie outside that ball. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma small_loop_no_single_crossing (c p : C(unitInterval,ℂ))
    (a : ℂ) (r : ℝ) (hr : 0<r) (hc : ∀ u, c u∈ball a r)
    (hp₀ : p 0∉ball a r) (hp₁ : p 1∉ball a r)
    (s t : unitInterval) (hs : 0<(s:ℝ) ∧ (s:ℝ)<1) (ht : 0<(t:ℝ) ∧ (t:ℝ)<1)
    (hcross : c t=p s) (hu : ∀ u v, c v=p u → u=s ∧ v=t)
    (hi : ∃ ρ : ℝ, 0<ρ ∧ InjOn (crossingSquareMap c p)
      (closedBall ((s:ℂ)+(t:ℂ)*Complex.I) ρ)) (hloop : c 0=c 1) : False := by
  obtain ⟨A,hA⟩ := continuous_log_on_ball_away a (p 0) r hr hp₀
  obtain ⟨B,hB⟩ := continuous_log_on_ball_away a (p 1) r hr hp₁
  let c' : C(unitInterval,ball a r) := ⟨fun u => ⟨c u,hc u⟩,c.continuous.subtype_mk _⟩
  have hc' : c' 0=c' 1 := Subtype.ext hloop
  have hbase (u : unitInterval) : c 0-p u≠0 := by
    intro he
    have he' := (hu u 0 (sub_eq_zero.mp he)).2
    have heR := congrArg (fun x : unitInterval => (x:ℝ)) he'
    simp only [Set.Icc.coe_zero] at heR
    linarith [ht.1]
  exact no_single_locally_injective_crossing c p s t hs ht hcross hu hi hloop hbase
    (A.comp c') (B.comp c') (fun u => hA (c' u)) (fun u => hB (c' u))
    (congrArg A hc') (congrArg B hc')

end SLEExactGauge

end

end OAI
