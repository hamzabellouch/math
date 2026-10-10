import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDyadPartition

namespace OAI

/-! Exact dyadic decomposition of both coefficient supports in the original
product-envelope tail. The triangle inequality is applied only after this
finite identity. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma envelopeCutoffBilinearTail_dyads (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X : ℝ) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∑ r ∈ P.image stoppedNormDyadIndex, ∑ s ∈ S.image stoppedNormDyadIndex,
        envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
          α β W H T X := by
  unfold envelopeCutoffBilinearTail
  have hb (v : ℕ) (a : Eisenstein) := stoppedNormDyad_partition S
    (fun b => α a*β b*gauss (a*b)*W (norm (a*b)/X)*
      heightFourierIntegral (fun t => cutoffHeightMultiplier H t*
        heightWindow (T*(3/2:ℝ)^v) t) (Real.log (norm (a*b))-Real.log X))
  simp_rw [hb]
  conv_lhs =>
    arg 2
    ext v
    rw [stoppedNormDyad_partition P]
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]

lemma envelopeCutoffBilinearTail_dyads_bound (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X M : ℝ)
    (hb : ∀ r ∈ P.image stoppedNormDyadIndex, ∀ s ∈ S.image stoppedNormDyadIndex,
      ‖envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
        α β W H T X‖ ≤ M) :
    ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
      ((P.image stoppedNormDyadIndex).card:ℝ)*
        ((S.image stoppedNormDyadIndex).card:ℝ)*M := by
  rw [envelopeCutoffBilinearTail_dyads]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun r hr => (norm_sum_le _ _).trans
    (Finset.sum_le_sum (hb r hr)))).trans_eq
  simp [mul_assoc]

theorem stoppedNormDyad_count_power :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (Q A B : ℝ),
      1 ≤ Q → 1 ≤ A → 1 ≤ B → A ≤ B^3 →
      (∀ a ∈ P, norm a ≤ Q*A) →
      ((P.image stoppedNormDyadIndex).card:ℝ) ≤
        (3*C*(1+Real.log Q))*(1+Real.log B) := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  refine ⟨C,hC,?_⟩
  intro P Q A B hQ hA hB hAB hP
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hm : Nat.log 2 ⌊Q*A⌋₊+1 ≤ Nat.log 2 ⌊3*(Q*A)⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
  apply (Nat.cast_le.mpr ((stoppedNormDyad_count P hP).trans hm)).trans
  apply (hcount (Q*A) (one_le_mul_of_one_le_of_one_le hQ hA)).trans
  rw [Real.log_mul hQp.ne' hAp.ne']
  have hlog := Real.log_le_log hAp hAB
  rw [Real.log_pow] at hlog
  have hq := Real.log_nonneg hQ
  have hb := Real.log_nonneg hB
  have hmul : 0 ≤ Real.log Q*Real.log B := mul_nonneg hq hb
  have hh : 1+Real.log Q+Real.log A ≤ 3*(1+Real.log Q)*(1+Real.log B) := by
    norm_num at hlog
    nlinarith
  nlinarith only [mul_le_mul_of_nonneg_left hh hC.le]

end CubicFirstMoment

end

end OAI
