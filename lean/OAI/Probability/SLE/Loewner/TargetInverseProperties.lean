import OAI.Probability.SLE.Loewner.TargetInverseExistence

namespace OAI

/-! Exact inverse identities for the raw flow on its surviving domain. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Target

lemma surviving_mem_upperHalfPlane (κ : ℝ) (b : Driver) (z : ℂ)
    (T : ℝ) (hT : 0 ≤ T) (hs : Surviving κ b z T) : z ∈ upperHalfPlane := by
  obtain ⟨j,hj,hmin⟩ := hs
  have hh := surviving_cutoff_height κ b z T j hj hmin 0 ⟨le_rfl,hT⟩
  rw [cutoffFlow_zero κ b j hj] at hh
  have hj0 : (0:ℝ)<j := by exact_mod_cast (Nat.succ_le_iff.mp hj)
  exact (inv_pos.mpr hj0).trans hh

lemma surviving_flow_mem_upperHalfPlane (κ : ℝ) (b : Driver) (z : ℂ)
    (T : ℝ) (hT : 0 ≤ T) (hs : Surviving κ b z T) :
    flow κ b z T ∈ upperHalfPlane := by
  have hj := (Nat.find_spec hs).1
  have hh := surviving_cutoff_height κ b z T (Nat.find hs) hj (Nat.find_spec hs).2 T ⟨hT,le_rfl⟩
  have hj0 : (0:ℝ)<Nat.find hs := by exact_mod_cast (Nat.succ_le_iff.mp hj)
  change 0 < (flow κ b z T).im
  rw [flow,dite_eq_left hs]
  exact (inv_pos.mpr hj0).trans hh

lemma inverseFlow_spec (κ : ℝ) (b : Driver) (T : ℝ) (w : ℂ)
    (hex : ∃ z, Surviving κ b z T ∧ flow κ b z T=w) :
    Surviving κ b (inverseFlow κ b T w) T ∧ flow κ b (inverseFlow κ b T w) T=w := by
  classical
  simpa only [inverseFlow,ite_eq_left hex] using Classical.epsilon_spec hex

lemma inverseFlow_eq_of_surviving (κ : ℝ) (b : Driver) (T : ℝ)
    (hT : 0 ≤ T) (z w : ℂ) (hz : Surviving κ b z T) (he : flow κ b z T=w) :
    inverseFlow κ b T w=z := by
  have hi := inverseFlow_spec κ b T w ⟨z,hz,he⟩
  exact flow_injOn_surviving κ b T hT hi.1 hz (hi.2.trans he.symm)

lemma inverseFlow_surviving (κ : ℝ) (hκ : 0 < κ) (b : Driver)
    (T : ℝ≥0) (w : ℂ) (hw : w ∈ upperHalfPlane) :
    Surviving κ b (inverseFlow κ b T w) T :=
  (inverseFlow_spec κ b T w (exists_surviving_preimage κ hκ b T w hw)).1

lemma flow_inverseFlow (κ : ℝ) (hκ : 0 < κ) (b : Driver)
    (T : ℝ≥0) (w : ℂ) (hw : w ∈ upperHalfPlane) :
    flow κ b (inverseFlow κ b T w) T=w :=
  (inverseFlow_spec κ b T w (exists_surviving_preimage κ hκ b T w hw)).2

lemma inverseFlow_mem_upperHalfPlane (κ : ℝ) (hκ : 0 < κ) (b : Driver)
    (T : ℝ≥0) (w : ℂ) (hw : w ∈ upperHalfPlane) :
    inverseFlow κ b T w ∈ upperHalfPlane :=
  surviving_mem_upperHalfPlane κ b _ T T.coe_nonneg (inverseFlow_surviving κ hκ b T w hw)

end SLEExactGauge.Target

end

end OAI
