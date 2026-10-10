import OAI.Probability.SLE.Loewner.TargetInverseProperties

namespace OAI

/-! Local stability and continuity of the raw inverse flow, independently of
the existence of a geometric trace. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma inverseFlow_eq_reverse_trajectory
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0) (w : ℂ)
    (η : ℝ) (hη : 0 < η) (hηw : η ≤ w.im) (Q : ℝ → ℂ)
    (hQ0 : Q 0=w)
    (hQd : ∀ s, 0 ≤ s → HasDerivWithinAt Q
      (reverseField η (driverValue b ((T:ℝ)-κ*s)) (Q s)) (Ici 0) s) :
    inverseFlow κ b T w=Q ((T:ℝ)/κ) := by
  have h := reverse_trajectory_preimage κ hκ b T w η hη hηw Q hQ0 hQd
  exact inverseFlow_eq_of_surviving κ b T T.coe_nonneg _ w h.1 h.2

lemma inverseFlow_lipschitzOn_height
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0)
    (η : ℝ) (hη : 0 < η) :
    LipschitzOnWith ⟨Real.exp ((4*η⁻¹^2)*((T:ℝ)/κ)), (Real.exp_pos _).le⟩
      (inverseFlow κ b T) {w : ℂ | η ≤ w.im} := by
  let U (s : ℝ) (_ : ℂ) := driverValue b ((T:ℝ)-κ*s)
  have hUc : Continuous (fun s : ℝ => driverValue b ((T:ℝ)-κ*s)) := by
    exact b.continuous.comp (continuous_real_toNNReal.comp
      (continuous_const.sub (continuous_const.mul continuous_id)))
  have hUm : Measurable (fun q : ℝ × ℂ => U q.1 q.2) :=
    hUc.measurable.comp measurable_fst
  obtain ⟨Q,_,hQ0,hQd⟩ := exists_measurable_reverse_flow U hUm
    (fun _ => hUc) id measurable_id hη
  have hQc (w : ℂ) : ContinuousOn (fun s => Q s w) (Icc 0 ((T:ℝ)/κ)) :=
    fun s hs => ((hQd w s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  have hQd' (w : ℂ) (s : ℝ) (hs : s ∈ Ico 0 ((T:ℝ)/κ)) :
      HasDerivWithinAt (fun r => Q r w)
        (reverseField η (driverValue b ((T:ℝ)-κ*s)) (Q s w)) (Ici s) s :=
    (hQd w s hs.1).mono (Ici_subset_Ici.mpr hs.1)
  have he (w : ℂ) (hw : η ≤ w.im) : inverseFlow κ b T w=Q ((T:ℝ)/κ) w :=
    inverseFlow_eq_reverse_trajectory κ hκ b T w η hη hw
      (fun s => Q s w) (hQ0 w) (hQd w)
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  rw [he z hz,he w hw]
  have h := dist_le_of_trajectories_ODE
    (fun s => reverseField_lipschitz hη (driverValue b ((T:ℝ)-κ*s)))
    (hQc z) (hQd' z) (hQc w) (hQd' w)
    (show dist (Q 0 z) (Q 0 w) ≤ dist z w by simp only [hQ0,id_eq]; exact le_rfl)
    ((T:ℝ)/κ) ⟨div_nonneg T.coe_nonneg hκ.le,le_rfl⟩
  change dist (Q ((T:ℝ)/κ) z) (Q ((T:ℝ)/κ) w) ≤
    dist z w * Real.exp ((4*η⁻¹^2)*((T:ℝ)/κ-0)) at h
  change dist (Q ((T:ℝ)/κ) z) (Q ((T:ℝ)/κ) w) ≤
    Real.exp ((4*η⁻¹^2)*((T:ℝ)/κ)) * dist z w
  simpa only [sub_zero,mul_comm] using h

lemma continuousOn_inverseFlow
    (κ : ℝ) (hκ : 0 < κ) (b : Driver) (T : ℝ≥0) :
    ContinuousOn (inverseFlow κ b T) upperHalfPlane := by
  intro w hw
  have hη : 0 < w.im/2 := half_pos hw
  have hLip := inverseFlow_lipschitzOn_height κ hκ b T (w.im/2) hη
  have hn : {z : ℂ | w.im/2 ≤ z.im} ∈ 𝓝 w := by
    have hn0 : {z : ℂ | w.im/2 < z.im} ∈ 𝓝 w :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
        (by change w.im/2 < w.im; exact half_lt_self hw)
    exact mem_of_superset hn0 (fun z hz => by
      change w.im/2 ≤ z.im
      exact (show w.im/2 < z.im from hz).le)
  exact (hLip.continuousOn.continuousAt hn).continuousWithinAt

end SLEExactGauge.Target

end

end OAI
