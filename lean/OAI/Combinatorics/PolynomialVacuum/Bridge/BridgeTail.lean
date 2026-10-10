import OAI.Combinatorics.HoneycombCorridor.BridgeFiniteness
import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeTailTarget

namespace OAI

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem bridgeWord_reaches (h : ℕ) (hh : 1 ≤ h) (p : BridgePath h) (t : ℝ) :
    reachesDistance t (bridgeWord h hh p) ↔ BridgeReaches p t := by
  simp only [reachesDistance,BridgeReaches,bridgeWord_trace]

theorem bridgeTailMass_bound (h : ℕ) (hh : 1 ≤ h) (t : ℝ) (ht : 0 ≤ t) :
    bridgeTailMass h t ≤ tailConstant * Real.exp (-tailRate*t/(h+1)) := by
  classical
  apply Real.tsum_le_of_sum_le (fun p => ite_nonneg (pow_nonneg criticalActivity_pos.le _) le_rfl)
  intro S
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
    (fun w => if reachesDistance t w then criticalActivity^w.length else 0)
    (fun w => ite_nonneg (pow_nonneg criticalActivity_pos.le _) le_rfl)
  simp only [bridgeWord_reaches,bridgeWord_length] at hM
  exact hM.trans (lateralMass_exp h hh _ (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht)

theorem bridgeTailLengthMass_bound (h : ℕ) (hh : 1 ≤ h) (t : ℝ) (ht : 0 ≤ t) :
    bridgeTailLengthMass h t ≤
      tailConstant*spatialConstant*((h : ℝ)+1)^2*Real.exp (-(tailRate/2)*t/(h+1)) := by
  classical
  apply Real.tsum_le_of_sum_le (fun p => ite_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _)) le_rfl)
  intro S
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
    (fun w => if reachesDistance t w then (w.length : ℝ)*criticalActivity^w.length else 0)
    (fun w => ite_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg criticalActivity_pos.le _)) le_rfl)
  simp only [bridgeWord_reaches,bridgeWord_length] at hM
  exact hM.trans (lateralLengthMass_exp h hh _ (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht)

theorem unrestricted_bridge_tail : UnrestrictedBridgeTail := by
  obtain ⟨C,c,hC,hc,hbound⟩ := finite_lateral_tail
  refine ⟨C,c,hC,hc,?_⟩
  intro h hh t ht
  classical
  constructor
  · apply Real.tsum_le_of_sum_le (fun p => ite_nonneg (pow_nonneg criticalActivity_pos.le _) le_rfl)
    intro S
    obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
      (fun w => if reachesDistance t w then criticalActivity^w.length else 0)
      (fun w => ite_nonneg (pow_nonneg criticalActivity_pos.le _) le_rfl)
    simp only [bridgeWord_reaches,bridgeWord_length] at hM
    exact hM.trans (hbound h _ hh (vertexWindow_convex h M)
      (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht).1
  · apply Real.tsum_le_of_sum_le (fun p => ite_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _)) le_rfl)
    intro S
    obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
      (fun w => if reachesDistance t w then (w.length : ℝ)*criticalActivity^w.length else 0)
      (fun w => ite_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg criticalActivity_pos.le _)) le_rfl)
    simp only [bridgeWord_reaches,bridgeWord_length] at hM
    exact hM.trans (hbound h _ hh (vertexWindow_convex h M)
      (bottomSource_mem_window h M hh) (vertexWindow_strip h M) t ht).2

end PolynomialVacuumBridge.Corridor

end OAI
