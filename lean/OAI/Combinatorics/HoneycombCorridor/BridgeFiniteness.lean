import Mathlib
import OAI.Combinatorics.HoneycombCorridor.LateralLength
import OAI.Combinatorics.HoneycombCorridor.Bridges

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_bridges_window (h : ℕ) (S : Finset (BridgePath h)) :
    ∃ M : ℕ, ∀ p ∈ S, ∀ v ∈ p.vertices, v ∈ vertexWindow h M := by
  classical
  let V := S.biUnion (fun p => p.vertices.toFinset)
  have hV : ∀ v ∈ V, InStrip h v := by
    intro v hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    have hi := p.inStrip v (List.mem_toFinset.mp hv)
    simpa only [InStrip,layer_boxIndex] using hi
  obtain ⟨M,hM⟩ := finite_vertices_in_window h V hV
  refine ⟨M,?_⟩
  intro p hp v hv
  exact hM (Finset.mem_biUnion.mpr ⟨p,hp,List.mem_toFinset.mpr hv⟩)

theorem bridge_finite_sum_word_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h))
    (f : List Bool → ℝ) (hf : ∀ w, 0 ≤ f w) :
    ∃ M : ℕ, (∑ p ∈ S, f (bridgeWord h hh p)) ≤
      ∑ w ∈ sourceExits (vertexWindow h M) bottomSource, f w := by
  classical
  obtain ⟨M,hM⟩ := finite_bridges_window h S
  refine ⟨M,?_⟩
  rw [← Finset.sum_image (fun p _ q _ he => bridgeWord_injective h hh he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => hf w)
  intro w hw
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
  exact bridgeWord_mem_sourceExits h hh p _ (vertexWindow_strip h M) (hM p hp)

theorem bridge_weight_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, weight p) ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S (fun w => criticalActivity^w.length)
    (fun w => pow_nonneg criticalActivity_pos.le _)
  simp only [bridgeWord_length] at hM
  apply hM.trans
  exact boundary_source_weight_bound _ bottomSource (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh)
    (bottomSource_outside_of_strip h _ (vertexWindow_strip h M))

theorem sourceExit_reaches_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) : reachesDistance 0 w := by
  cases w with
  | nil =>
    have hn := ((mem_sourceExits _ _ _).mp hw).1
    exact False.elim (hn hg)
  | cons b w => exact ⟨bottomSource.1,by simp [traced],abs_nonneg _⟩

theorem lateralLengthMass_zero (D : Finset Vertex) (hg : bottomSource.1 ∈ D) :
    lateralLengthMass D 0 = ∑ w ∈ sourceExits D bottomSource,
      (w.length : ℝ)*criticalActivity^w.length := by
  classical
  unfold lateralLengthMass
  apply Finset.sum_congr rfl
  intro w hw
  simp only [sourceExit_reaches_zero D hg w hw,ite_true]

theorem bridge_length_finite_sum_bound (h : ℕ) (hh : 1 ≤ h) (S : Finset (BridgePath h)) :
    (∑ p ∈ S, firstLengthWeight p) ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 := by
  obtain ⟨M,hM⟩ := bridge_finite_sum_word_bound h hh S
    (fun w => (w.length : ℝ)*criticalActivity^w.length)
    (fun w => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg criticalActivity_pos.le _))
  simp only [bridgeWord_length] at hM
  rw [← lateralLengthMass_zero _ (bottomSource_mem_window h M hh)] at hM
  apply hM.trans
  have ht := lateralLengthMass_exp h hh _ (vertexWindow_convex h M)
    (bottomSource_mem_window h M hh) (vertexWindow_strip h M) 0 le_rfl
  simpa only [mul_zero,zero_div,Real.exp_zero,mul_one] using ht

theorem bridge_weight_summable (h : ℕ) (hh : 1 ≤ h) : Summable (weight (h := h)) := by
  refine summable_of_sum_le (f := weight (h := h))
    (c := (Real.cos (3*Real.pi/8))⁻¹) ?_ (bridge_weight_finite_sum_bound h hh)
  intro p
  exact pow_nonneg criticalActivity_pos.le p.vertices.length

theorem bridge_length_summable (h : ℕ) (hh : 1 ≤ h) : Summable (firstLengthWeight (h := h)) := by
  refine summable_of_sum_le (f := firstLengthWeight (h := h))
    (c := tailConstant*spatialConstant*((h : ℝ)+1)^2) ?_
    (bridge_length_finite_sum_bound h hh)
  intro p
  exact mul_nonneg (Nat.cast_nonneg p.vertices.length)
    (pow_nonneg criticalActivity_pos.le p.vertices.length)

theorem finite_bridge_sums : FiniteBridgeSums := by
  intro h hh
  have hm := bridge_weight_summable h hh
  have hl := bridge_length_summable h hh
  have hmc : Summable (fun p : ConfinedBridgePath h => weight p.val) := hm.subtype InLogCorridor
  have hlc : Summable (fun p : ConfinedBridgePath h => firstLengthWeight p.val) := hl.subtype InLogCorridor
  exact ⟨hm,hl,hl.div_const _,hmc,hlc,hlc.div_const _⟩

end PolynomialVacuumBridge.Corridor

end

end OAI
