import OAI.NumberTheory.Jacobsthal.Renewal.ClockTailReward

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal

lemma spacing_tail_exponential {eta : ℝ} (heta : 0 < eta) (a : ℝ) :
    markedSpacingLaw (Ioi a) ≤ ENNReal.ofReal (Real.exp (-eta*a))*costTransform markedSpacingLaw eta := by
  calc
    _ = ∫⁻ G, (Ioi a).indicator (fun _ => (1:ℝ≥0∞)) G ∂markedSpacingLaw := by
      rw [lintegral_indicator measurableSet_Ioi]
      simp
    _ ≤ ∫⁻ G, ENNReal.ofReal (Real.exp (-eta*a))*ENNReal.ofReal (Real.exp (eta*G)) ∂markedSpacingLaw := by
      apply lintegral_mono
      intro G
      by_cases hG : G ∈ Ioi a
      · rw [indicator_of_mem hG]
        change (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-eta*a))*ENNReal.ofReal (Real.exp (eta*G))
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        have he : (1:ℝ) ≤ Real.exp (-eta*a+eta*G) := Real.one_le_exp_iff.mpr (by change a<G at hG; nlinarith)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
      · rw [indicator_of_notMem hG]
        exact zero_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma exponential_tail_sum (eta H : ℝ) :
    (∑' j : ℕ, ENNReal.ofReal (Real.exp (-eta*(H+j)))) =
      ENNReal.ofReal (Real.exp (-eta*H))*(1-ENNReal.ofReal (Real.exp (-eta)))⁻¹ := by
  have he (j : ℕ) : ENNReal.ofReal (Real.exp (-eta*(H+j))) =
      ENNReal.ofReal (Real.exp (-eta*H))*(ENNReal.ofReal (Real.exp (-eta)))^j := by
    have hp : Real.exp (-eta*(j:ℝ)) = (Real.exp (-eta))^j := by
      rw [← Real.rpow_natCast (Real.exp (-eta)) j,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    rw [show -eta*(H+(j:ℝ)) = -eta*H+(-eta*(j:ℝ)) by ring,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le,hp,ENNReal.ofReal_pow (Real.exp_pos _).le]
  simp_rw [he]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]

lemma spacing_tail_series_bound {eta : ℝ} (heta : 0 < eta) (H : ℝ) :
    (∑' j : ℕ, markedSpacingLaw (Ioi (H+j))) ≤
      costTransform markedSpacingLaw eta*(1-ENNReal.ofReal (Real.exp (-eta)))⁻¹*
        ENNReal.ofReal (Real.exp (-eta*H)) := by
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-eta*(H+j)))*costTransform markedSpacingLaw eta :=
      ENNReal.tsum_le_tsum (fun j => spacing_tail_exponential heta (H+j))
    _ = (∑' j : ℕ, ENNReal.ofReal (Real.exp (-eta*(H+j))))*costTransform markedSpacingLaw eta := ENNReal.tsum_mul_right
    _ = _ := by rw [exponential_tail_sum]; ac_rfl

theorem clockOvershoot_exponential : ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧ ∀ v H : ℝ,
    0 < v → 0 ≤ H → clockOvershoot v H ≤ ENNReal.ofReal (C*Real.exp (-eta*H)) := by
  obtain ⟨eta,heta,_hWait,hMoment⟩ := marked_waiting_common_exponential_moment
  obtain ⟨B,hB,hreward⟩ := clock_renewal_reward_tail_bound
  let r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-eta))
  have hr : r < 1 := by
    dsimp [r]
    exact ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hInv : (1-r)⁻¹ < ∞ := lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hr).ne')
  let K : ℝ≥0∞ := ENNReal.ofReal B*costTransform markedSpacingLaw eta*(1-r)⁻¹
  have hK : K < ∞ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hMoment) hInv
  let C : ℝ := K.toReal+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      _ = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨eta,C,heta,hC,?_⟩
  intro v H hv _hH
  calc
    _ ≤ ENNReal.ofReal B*(∑' j : ℕ, markedSpacingLaw (Ioi (H+j))) :=
      (clockOvershoot_le_reward hv H).trans (hreward v H)
    _ ≤ ENNReal.ofReal B*(costTransform markedSpacingLaw eta*(1-r)⁻¹*
        ENNReal.ofReal (Real.exp (-eta*H))) := mul_le_mul_right (spacing_tail_series_bound heta H) _
    _ = K*ENNReal.ofReal (Real.exp (-eta*H)) := by dsimp [K]; ac_rfl
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (Real.exp (-eta*H)) := mul_le_mul_left hKC _
    _ = _ := (ENNReal.ofReal_mul hC.le).symm

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
