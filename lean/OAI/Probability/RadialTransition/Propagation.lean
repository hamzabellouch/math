import OAI.Probability.RadialTransition.PressureBall

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma parameter_shift_dist (x y : Parameter) (z : ℝ) :
    dist (parameter (x 0) (x 1+z)) (parameter (y 0) (y 1+z))=dist x y := by
  rw [dist_eq_norm,parameter_sub,dist_eq_norm]
  congr 1
  ext i
  fin_cases i <;> simp

lemma parameter_shift_dist_self (x : Parameter) (z : ℝ) :
    dist (parameter (x 0) (x 1+z)) x=|z| := by
  rw [← parameter_eta x,dist_eq_norm,parameter_sub]
  simp only [parameter_zero,parameter_one,sub_self,add_sub_cancel_left]
  exact parameter_vertical_norm z

lemma phaseWindow_shift {x : Parameter} {r z : ℝ} (hx : x ∈ phaseWindow r) :
    parameter (x 0) (x 1+z) ∈ phaseWindow (r+|z|) :=
  phaseWindow_near hx (by rw [Metric.mem_closedBall,parameter_shift_dist_self])

lemma propagate_phase_groups {P Q : Pressure} {a δ C U k l r s : ℝ}
    (hP : ConvexOn ℝ positiveParameters (onParameters P))
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (ha : 0 < a) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hk : 0 < k) (hl : 0 < l) (hr : 0 ≤ r) (hs : s ≤ 1/4)
    (hgap : 2*(k+2*δ/(k*a)+2*C*l/k+r)<packingDensity)
    (hgroups : ∀ y ∈ phaseWindow s, HasPhaseGroups P y r)
    (happ : ∀ y ∈ phaseWindow (1/4), |onParameters Q y-onParameters P y| ≤ δ)
    (hlip : ∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
      |onParameters P x-onParameters P y| ≤ C*dist x y)
    (hact : ∀ β h, 0 < β → ∃ u, ActiveShift Q a β h u)
    (hcut : ∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (x 0) (x 1) u) :
    ∀ w ∈ phaseWindow (s-(5/4*U+k+l+1)*a),
      HasPhaseGroups (idealAttraction Q a) w (r+2*δ/(l*a)+a*U^2/2) := by
  intro w hw
  let S := 5/4*U+k+l+1
  have hS : 0 < S := by dsimp [S]; positivity
  have hwq : w ∈ phaseWindow (1/4) := phaseWindow_mono (by dsimp [S] at hS; nlinarith) hw
  obtain ⟨hwβ, _⟩ := phaseWindow_quarter_bounds hwq
  have hwβ0 : 0 < w 0 := by linarith [hwβ.1]
  have hlocal : ∀ y ∈ Metric.closedBall w (1/16), ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a (y 0) (y 1) u := by
    intro y hy
    exact hcut y (phaseWindow_mono (by norm_num : (1/4:ℝ)+1/16≤1/2) (phaseWindow_near hwq hy))
  have hgen := ideal_supportSet_generated hQ ha hact (by norm_num : (0:ℝ)<1/16)
    (by linarith [hwβ.1] : 2*(1/16:ℝ)<w 0) hlocal
  apply phase_groups_of_generators hgen
  rintro v ⟨u, hub, hu, e, he, rfl⟩
  let x := parameter (w 0) (w 1+w 0*a*u)
  have hxu : dist x w ≤ 5/4*U*a := by
    rw [parameter_shift_dist_self,abs_of_nonneg (by exact mul_nonneg (mul_nonneg hwβ0.le ha.le) hub.1 : 0 ≤ w 0*a*u)]
    have hm := mul_le_mul hwβ.2 hub.2 hub.1 (by norm_num : (0:ℝ)≤5/4)
    nlinarith [mul_le_mul_of_nonneg_right hm ha.le]
  have htest (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) (z : ℝ) (hz : |z| ≤ k*a) :
      parameter (y 0) (y 1+z) ∈ phaseWindow s := by
    change dist (parameter (y 0) (y 1+z)) phaseCenter ≤ s
    have h1 := dist_triangle (parameter (y 0) (y 1+z)) y phaseCenter
    rw [parameter_shift_dist_self] at h1
    have h2 := dist_triangle y x phaseCenter
    have h3 := dist_triangle x w phaseCenter
    have hy' := Metric.mem_closedBall.mp hy
    have hw' := Metric.mem_closedBall.mp hw
    change dist w phaseCenter ≤ s-S*a at hw'
    dsimp [S] at hw'
    nlinarith
  have hbase (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) : y ∈ phaseWindow s := by
    have hh := htest y hy 0 (by simp; positivity)
    simpa only [add_zero,parameter_eta] using hh
  have hbaseq (y : Parameter) (hy : y ∈ Metric.closedBall x (l*a)) : y ∈ phaseWindow (1/4) :=
    phaseWindow_mono hs (hbase y hy)
  have hxball : x ∈ Metric.closedBall x (l*a) := Metric.mem_closedBall_self (by positivity)
  have hsp : phaseWindow s ⊆ positiveParameters := by
    intro y hy
    exact phaseWindow_positive (by linarith) hy
  let b := k+2*δ/(k*a)+2*C*l/k
  have hband : ∀ y ∈ Metric.closedBall x (l*a),
      ∀ v ∈ supportSet (onParameters P) positiveParameters y, |v 1-u| ≤ b := by
    intro y hy v hv
    have hzbound (z : ℝ) (hz : z ∈ ({0,k*a,-(k*a)} : Set ℝ)) : |z| ≤ k*a := by
      simp only [mem_insert_iff,mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp; positivity
      · rw [abs_of_pos (mul_pos hk ha)]
      · rw [abs_neg,abs_of_pos (mul_pos hk ha)]
    have hhh := active_neighborhood_density_band ha hwβ0 (hsp (hbase y hy)) (mul_pos hk ha) hu
      (pressureSupport_iff.mpr hv)
      (fun z hz => happ _ (phaseWindow_mono hs (htest x hxball z (hzbound z hz))))
      (fun z hz => by
        have hp := hlip _ (phaseWindow_mono hs (htest y hy z (hzbound z hz)))
          _ (phaseWindow_mono hs (htest x hxball z (hzbound z hz)))
        rw [parameter_shift_dist] at hp
        exact hp.trans (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) hC))
    apply hhh.trans
    have hfirst : k*a/(2*w 0*a) ≤ k := by
      apply (div_le_iff₀ (by positivity : 0 < 2*w 0*a)).mpr
      have hm := mul_le_mul_of_nonneg_right (show 1 ≤ 2*w 0 by linarith [hwβ.1]) (mul_nonneg hk.le ha.le)
      nlinarith only [hm]
    have heq : 2*C*(l*a)/(k*a)=2*C*l/k := by field_simp
    rw [heq]
    dsimp [b]
    linarith
  obtain ⟨i,hi⟩ := common_group_of_density_band
    (fun y => supportSet (onParameters P) positiveParameters y)
    (Metric.closedBall x (l*a)) phaseSlope (fun v => v 1) ⟨x,hxball⟩
    (fun y hy => hgroups y (hbase y hy))
    (fun y hy => supportSet_nonempty isOpen_positiveParameters hP (hsp (hbase y hy)))
    hband (fun v w => by simpa only [PiLp.sub_apply,dist_eq_norm] using parameter_coord_abs_le (v-w) 1)
    phase_densities_separated hgap
  have he' : parameter e u ∈ supportSet (onParameters Q) positiveParameters x := by
    apply pressureSupport_iff.mp
    exact he
  have hnorm := support_transfer_bound (onParameters P) (onParameters Q) positiveParameters x (phaseSlope i)
    (parameter e u) (mul_pos hl ha) hr hδ (fun y hy => hsp (hbase y hy))
    (fun y hy => happ y (hbaseq y hy))
    (fun y hy => by
      obtain ⟨v,hv⟩ := supportSet_nonempty isOpen_positiveParameters hP (hsp (hbase y hy))
      exact ⟨v,hv,hi y hy hv⟩) he'
  have hsq : u^2 ≤ U^2 := (sq_le_sq₀ hub.1 hU).mpr hub.2
  refine ⟨i, Metric.mem_closedBall.mpr ?_⟩
  rw [dist_eq_norm]
  have heq : parameter (e+a*u^2/2) u-phaseSlope i =
      (parameter e u-phaseSlope i)+parameter (a*u^2/2) 0 := by
    ext j
    fin_cases j <;> simp
    ring
  rw [heq]
  have hnorm' := norm_add_le (parameter e u-phaseSlope i) (parameter (a*u^2/2) 0)
  rw [parameter_horizontal_norm,abs_of_nonneg (by positivity : 0 ≤ a*u^2/2)] at hnorm'
  nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]

end RadialTransition
end

end OAI
