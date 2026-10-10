import OAI.Probability.SLE.Loewner.LocalReverseCone
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! The initial cone only uses the driving derivative inside its interval;
no continuation of that derivative beyond the terminal time is needed. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

lemma exists_initial_reverse_cone_of_interval_derivative {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hqc : ContinuousOn q (Icc 0 T))
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (u' t) (Icc 0 T) t)
    (hq0 : q 0=(u 0 : ℂ))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hqp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hb : ∀ t ∈ Icc 0 T, |u' t| ≤ L) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧
      ∀ t ∈ Icc 0 a, ((q t).re-u t)^2 ≤ t ∧ 3*t ≤ (q t).im^2 := by
  have hhalf : T/2 < T := half_lt_self hT
  have hsub : Icc 0 (T/2) ⊆ Icc 0 T := Icc_subset_Icc_right hhalf.le
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 (T/2)) : t ∈ Ioc 0 T :=
    ⟨ht.1,ht.2.trans hhalf.le⟩
  obtain ⟨a,ha,haT,hcone⟩ := exists_initial_reverse_cone (half_pos hT) hL q u u'
    (hqc.mono hsub) (fun t ht => (hu t (hsub ht)).continuousWithinAt.mono hsub) hq0
    (fun t ht => hq t (hpos t ht))
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ⟨ht.1.le,ht.2.trans_lt hhalf⟩
      (hu t ⟨ht.1.le,ht.2.trans hhalf.le⟩))
    (fun t ht => hqp t (hpos t ht)) (fun t ht => hb t ⟨ht.1.le,ht.2.trans hhalf.le⟩)
  exact ⟨a,ha,haT.trans hhalf.le,hcone⟩

end SLEExactGauge

end

end OAI
