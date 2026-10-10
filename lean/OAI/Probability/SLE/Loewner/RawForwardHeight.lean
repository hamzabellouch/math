import OAI.Probability.SLE.Angle.TargetFlowEvolution
import OAI.Probability.SLE.Loewner.RawSurvivingMonotone

namespace OAI

/-! Continuity and height monotonicity of the exact raw forward flow on
each surviving interval, without a geometric trace witness. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

lemma flow_continuousOn_of_survival (κ : ℝ) (b : Driver) (z : ℂ)
    {T : ℝ} (hT : 0 ≤ T) (hs : Surviving κ b z T) :
    ContinuousOn (flow κ b z) (Icc 0 T) := by
  obtain ⟨j,hj,hmin⟩ := hs
  apply ((cutoffFlow_continuousOn κ b j hj z).mono Icc_subset_Ici_self).congr
  intro t ht
  exact flow_eq_cutoff_on_interval κ b z T hT j hj hmin t ht

lemma flow_height_antitone_of_survival (b : Driver) (z : ℂ)
    {T : ℝ} (hT : 0 ≤ T) (hs : Surviving 1 b z T) :
    AntitoneOn (fun t => (flow 1 b z t).im) (Icc 0 T) := by
  have hc := Complex.continuous_im.comp_continuousOn (flow_continuousOn_of_survival 1 b z hT hs)
  have hd (t : ℝ) (ht : t ∈ interior (Icc 0 T)) :
      HasDerivWithinAt (fun s => (flow 1 b z s).im)
        (-2*(flow 1 b z t).im/Complex.normSq (flow 1 b z t-(driverValue b t : ℂ)))
        (interior (Icc 0 T)) t := by
    have hti : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t
      (flow_hasDerivWithinAt_of_later_survival 1 b z t T hti.1.le hti.2 hs)
    change HasDerivWithinAt (fun s => (flow 1 b z s).im)
      (((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))).im) (Ici 0) t at hh
    have he : ((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))).im =
        -2*(flow 1 b z t).im/Complex.normSq (flow 1 b z t-(driverValue b t : ℂ)) := by
      simp [a,Complex.div_im]
      ring
    rw [he] at hh
    exact hh.mono (interior_subset.trans Icc_subset_Ici_self)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hc hd
  intro t ht
  have hti : t ∈ Icc 0 T := interior_subset ht
  have hp := surviving_flow_mem_upperHalfPlane 1 b z t hti.1
    (surviving_of_le_time 1 b z hti.1 hti.2 hs)
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le) (Complex.normSq_nonneg _)

end SLEExactGauge.Target

end

end OAI
