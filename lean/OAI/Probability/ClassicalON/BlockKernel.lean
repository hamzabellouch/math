import OAI.Probability.ClassicalON.BlockOrbit

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def blockCoupling (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) : E → ℝ :=
  fun e => b e*blockRadius k (s (left e))*blockRadius k (s (right e))

def blockTailEnergy (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) : ℝ :=
  ∑ e,b e*⟪blockTail k (s (left e)),blockTail k (s (right e))⟫_ℝ

omit [Fintype V] [Fintype E] in
theorem blockCoupling_bounds (k : ℕ) (left right : E → V) (b : E → ℝ) (hb : ∀ e,0 ≤ b e)
    (s : V → Spin (3+k)) (e : E) : 0 ≤ blockCoupling k left right b s e ∧ blockCoupling k left right b s e ≤ b e := by
  unfold blockCoupling
  constructor
  · exact mul_nonneg (mul_nonneg (hb e) (blockRadius_nonneg _ _)) (blockRadius_nonneg _ _)
  · calc
      _ ≤ b e*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left (blockRadius_le_one _ _) (hb e))
        (blockRadius_le_one _ _) (blockRadius_nonneg _ _) (by simpa using hb e)
      _ = b e := by ring

omit [Fintype V] in
theorem blockFiberConfiguration_energy (k : ℕ) (left right : E → V) (b : E → ℝ)
    (s : V → Spin (3+k)) (t : V → Spin 3) :
    freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t)=
      freeSpinEnergy 3 left right (blockCoupling k left right b s) t+blockTailEnergy k left right b s := by
  unfold freeSpinEnergy blockTailEnergy blockFiberConfiguration
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [blockFiber_inner]
  unfold blockCoupling
  ring

omit [Fintype V] [Fintype E] in
theorem blockFiberConfiguration_first (k : ℕ) (x y : V) (s : V → Spin (3+k)) (t : V → Spin 3) :
    coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y (blockFiberConfiguration k s t)=
      (blockRadius k (s x)*blockRadius k (s y))*firstSpinProduct x y t := by
  unfold coordinateSpinProduct blockFiberConfiguration
  rw [← blockHead_first,← blockHead_first,blockHead_fiber,blockHead_fiber]
  simp only [PiLp.smul_apply,smul_eq_mul,firstSpinProduct]
  ring

def freeSpinPartition (n : ℕ) (left right : E → V) (b : E → ℝ) : ℝ :=
  ∫ s,Real.exp (freeSpinEnergy n left right b s) ∂freeSpinReference n

theorem freeSpinPartition_pos (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ) :
    0 < freeSpinPartition n left right b :=
  compact_integral_pos (continuous_freeSpinEnergy _ _ _ _).rexp (fun _ => Real.exp_pos _)

theorem block_fiber_partition (k : ℕ) (left right : E → V) (b : E → ℝ) (s : V → Spin (3+k)) :
    (∫ t,Real.exp (freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t)) ∂freeSpinReference 3)=
      Real.exp (blockTailEnergy k left right b s)*freeSpinPartition 3 left right (blockCoupling k left right b s) := by
  simp_rw [blockFiberConfiguration_energy,Real.exp_add]
  rw [integral_mul_const]
  exact mul_comm _ _

theorem block_fiber_numerator (k : ℕ) (left right : E → V) (b : E → ℝ)
    (x y : V) (s : V → Spin (3+k)) :
    (∫ t,Real.exp (freeSpinEnergy (3+k) left right b (blockFiberConfiguration k s t))*
      coordinateSpinProduct (3+k) ⟨0,by omega⟩ x y (blockFiberConfiguration k s t) ∂freeSpinReference 3)=
      (Real.exp (blockTailEnergy k left right b s)*freeSpinPartition 3 left right (blockCoupling k left right b s))*
        ((blockRadius k (s x)*blockRadius k (s y))*
          freeSpinMean 3 left right (blockCoupling k left right b s) (firstSpinProduct x y)) := by
  have hz := (freeSpinPartition_pos 3 left right (blockCoupling k left right b s)).ne'
  simp_rw [blockFiberConfiguration_energy,Real.exp_add,blockFiberConfiguration_first]
  have he (t : V → Spin 3) :
      Real.exp (freeSpinEnergy 3 left right (blockCoupling k left right b s) t)*
        Real.exp (blockTailEnergy k left right b s)*
          (blockRadius k (s x)*blockRadius k (s y)*firstSpinProduct x y t)=
      (Real.exp (blockTailEnergy k left right b s)*(blockRadius k (s x)*blockRadius k (s y)))*
        (Real.exp (freeSpinEnergy 3 left right (blockCoupling k left right b s) t)*firstSpinProduct x y t) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  unfold freeSpinMean weightedMean
  change _=(_*freeSpinPartition 3 left right (blockCoupling k left right b s))*
    (_*(_/freeSpinPartition 3 left right (blockCoupling k left right b s)))
  field_simp

end ClassicalON

end

end OAI
