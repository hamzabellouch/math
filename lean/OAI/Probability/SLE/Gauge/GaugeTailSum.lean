import OAI.Probability.SLE.Geometry.FiniteLawTailENN

namespace OAI

/-! The prescribed gauge entries retain their multiplicities when tail
probabilities are summed. Cleanup entries occur exactly once per batch. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge.Target

abbrev TailCode (κ : ℝ) (W : WienerLaw) :=
  ℕ ⊕ (Σ n : ℕ, Σ k : ℤ, Fin (multiplicity κ W (n+1) k))

def gaugeTailEquiv (κ : ℝ) (W : WienerLaw) : GaugeIndex κ W ≃ TailCode κ W where
  toFun e := match h : e.val.2 with
    | none => Sum.inl (e.val.1-1)
    | some (k,j) => Sum.inr ⟨e.val.1-1,k,j,by
        have hj := e.property.2
        rw [h] at hj
        simpa only [Nat.sub_add_cancel e.property.1] using hj⟩
  invFun c := match c with
    | Sum.inl n => ⟨(n+1,none),by simp [ValidEntry]⟩
    | Sum.inr ⟨n,k,j⟩ => ⟨(n+1,some (k,j.val)),by
        exact ⟨by omega,j.isLt⟩⟩
  left_inv e := by
    apply Subtype.ext
    rcases e with ⟨⟨n,o⟩,hn,ho⟩
    cases o with
    | none => simp only [Nat.sub_add_cancel hn]
    | some p => rcases p with ⟨k,j⟩; simp only [Nat.sub_add_cancel hn]
  right_inv c := by
    cases c with
    | inl n => simp
    | inr p => rcases p with ⟨n,k,j⟩; simp

lemma gauge_tail_sum_eq (κ : ℝ) (W : WienerLaw) (p : ℝ → ℝ≥0∞) :
    (∑' e : GaugeIndex κ W, p (16*weights κ W e)) =
      (∑' n : ℕ, p (16*((n:ℝ)+1))) +
      ∑' n : ℕ, ∑' k : ℤ, (multiplicity κ W (n+1) k : ℝ≥0∞)*
        p (16*MomentBatches.dyadic k) := by
  rw [← (gaugeTailEquiv κ W).symm.tsum_eq (fun e => p (16*weights κ W e))]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  congr 1
  · apply tsum_congr
    intro n
    simp [gaugeTailEquiv,weights,entryValue]
  · rw [ENNReal.tsum_sigma']
    apply tsum_congr
    intro n
    rw [ENNReal.tsum_sigma']
    apply tsum_congr
    intro k
    simp [gaugeTailEquiv,weights,entryValue,MomentBatches.dyadic,tsum_fintype]

end SLEExactGauge.Target

end

end OAI
