import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningLedger

namespace OAI

/-! # Cancellation of the dyadic weights in the simultaneous pruning costs -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem pruning_weight_cancel {H C w : ℝ≥0∞}
    (hH : H ≠ 0) (hw : w ≠ 0) (hwtop : w ≠ ∞) :
    (H*w)⁻¹*(C*w) = H⁻¹*C := by
  rw [ENNReal.mul_inv (Or.inl hH) (Or.inr hw)]
  calc
    H⁻¹*w⁻¹*(C*w) = (H⁻¹*C)*(w⁻¹*w) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hw hwtop,mul_one]

theorem pruning_weighted_sum {H C : ℝ≥0∞} (hH : H ≠ 0)
    (w : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ 0) (hwtop : ∀ i, w i ≠ ∞) :
    (∑ i, (H*w i)⁻¹*(C*w i)) = (Fintype.card ι : ℝ≥0∞)*(H⁻¹*C) := by
  simp_rw [pruning_weight_cancel hH (hw _) (hwtop _)]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem pruning_weighted_sum_le {H C : ℝ≥0∞} (hH : H ≠ 0)
    (w B : ι → ℝ≥0∞) (hw : ∀ i, w i ≠ 0) (hwtop : ∀ i, w i ≠ ∞)
    (hB : ∀ i, B i ≤ C*w i) :
    (∑ i, (H*w i)⁻¹*B i) ≤ (Fintype.card ι : ℝ≥0∞)*(H⁻¹*C) := by
  apply (Finset.sum_le_sum (fun i _ => mul_le_mul_right (hB i) _)).trans_eq
  exact pruning_weighted_sum hH w hw hwtop

theorem pruning_real_weighted_sum {H C : ℝ} (hH : 0 < H)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (H*w i))⁻¹*B i) ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)*C/H) := by
  have hi (i : ι) : (ENNReal.ofReal (H*w i))⁻¹*B i ≤ ENNReal.ofReal (C/H) := by
    apply (mul_le_mul_right (hB i) _).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (C*w i) / ENNReal.ofReal (H*w i) = _
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hH (hw i))]
    congr 1
    field_simp [(hw i).ne']
  calc
    _ ≤ ∑ _i : ι, ENNReal.ofReal (C/H) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card ι:ℝ≥0∞)*ENNReal.ofReal (C/H) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by
      rw [show (Fintype.card ι:ℝ≥0∞) = ENNReal.ofReal (Fintype.card ι:ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
