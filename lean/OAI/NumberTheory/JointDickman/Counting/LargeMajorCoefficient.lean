import OAI.NumberTheory.JointDickman.Counting.MajorCoefficientBound
import OAI.NumberTheory.JointDickman.Arithmetic.TotientLogBound
import OAI.NumberTheory.JointDickman.Arithmetic.SmoothCoefficientMinorArc

namespace OAI

/-! # Suppression of coefficient sums on the larger-denominator major arcs -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientExponentialSum_eq_smooth (B q : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (ξ X : ℝ) (w : ℝ → ℝ) :
    coefficientExponentialSum B q u ξ X w =
      smoothCoefficientAdditiveSum B X (((u : ZMod q).val : ℝ)/q+ξ/X) w := by
  unfold coefficientExponentialSum smoothCoefficientAdditiveSum
  apply tsum_congr
  intro n
  congr 2
  ring

theorem coefficient_large_majorArc_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ a b ε : ℝ, 0 < a → a ≤ b → 0 < ε →
      ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      Real.log X ∈ Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B) →
      ∀ (q : ℕ) [NeZero q], q ≤ B^15 → (B : ℝ)^(2/5 : ℝ) ≤ q →
      ∀ u : (ZMod q)ˣ, ∀ (w w' : ℝ → ℝ) (M N ξ : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) → |ξ| ≤ (B : ℝ)^(14 : ℝ) →
      ‖coefficientExponentialSum B q u ξ X w‖ ≤
        (D*M*(b-a)+K*b*(2*M+(N+2*Real.pi*M)*(b-a)))*X*(B : ℝ)^(-2/5+ε) := by
  obtain ⟨D,K,hD,hK,hbound⟩ := coefficient_majorArc_norm_bound hSD hSW hM hMP
  refine ⟨D,K,hD,hK,?_⟩
  intro a b ε ha hab hε
  filter_upwards [hbound a b ha hab,majorArc_totient_power hMP hε,eventually_ge_atTop 1]
    with B hboundB hφB hB
  intro X hX hlog q _ hq hqlo u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ
  have hqreal : (q : ℝ) ≤ (B : ℝ)^(15 : ℝ) := by
    norm_cast
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hφ := hφB q (NeZero.pos q) hq hqlo
  have hpow : (B : ℝ)^(-50 : ℝ) ≤ (B : ℝ)^(-2/5+ε) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hDM : 0 ≤ D*M*(b-a) := mul_nonneg (mul_nonneg hD hM0) (sub_nonneg.mpr hab)
  have hnorm : 0 ≤ K*b*(2*M+(N+2*Real.pi*M)*(b-a)) := by
    have hb : 0 < b := ha.trans_le hab
    positivity
  refine (hboundB X hX hlog q hqreal u w w' M N ξ hM0 hN hw hw' hbw hbw' hsupp hξ).trans ?_
  calc
    _ ≤ X*(D*M*(b-a)*(B : ℝ)^(-2/5+ε)+
        K*b*(2*M+(N+2*Real.pi*M)*(b-a))*(B : ℝ)^(-2/5+ε)) := by
      apply mul_le_mul_of_nonneg_left _ hX.le
      apply add_le_add
      · simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hφ hDM
      · exact mul_le_mul_of_nonneg_left hpow hnorm
    _ = _ := by ring

end JointDickman

end OAI
