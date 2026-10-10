import Mathlib
import OAI.Analysis.LaughlinGap.AuxiliaryComparison
import OAI.Analysis.LaughlinGap.FourSpin
import OAI.Analysis.LaughlinGap.RealSpinSquare

namespace OAI

/-! Three Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def threeWeightCoefficientStar (z T p : ℕ) : ℝ :=
  if z ≤ T then monomialWeight T p *
    (couplingPolynomial (1/Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3) z (T-z)).coeff p else 0

lemma threeWeightCoefficient_tendsto (z T p : ℕ) :
    Tendsto (fun Q => threeWeightCoefficient Q z T p) atTop
      (𝓝 (threeWeightCoefficientStar z T p)) := by
  by_cases hz : z ≤ T
  · have hr : Tendsto (fun Q : ℕ => (Q:ℝ) / (2*Q-2:ℕ)) atTop (𝓝 (1/2:ℝ)) := by
      simpa [Nat.sub_zero] using fallingFactor_tendsto 0
    have hu : Real.sqrt (1/2:ℝ) / Real.sqrt (1+(1/2:ℝ)) = 1/Real.sqrt 3 := by
      rw [show (1:ℝ)+1/2=3/2 by norm_num, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),
        Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_one]
      field_simp
    have hv : 1 / Real.sqrt (1+(1/2:ℝ)) = Real.sqrt 2 / Real.sqrt 3 := by
      rw [show (1:ℝ)+1/2=3/2 by norm_num, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
      field_simp
    have h := coupledCoefficient_tendsto_polynomial (by norm_num : (0:ℝ) ≤ 1/2)
      (affine_twice_spin_tendsto 1) hr z (T-z) p
    simpa only [threeWeightCoefficient,threeWeightCoefficientStar,ite_eq_left hz,
      Nat.add_sub_of_le hz,hu,hv,mul_one] using h
  · simp only [threeWeightCoefficient,threeWeightCoefficientStar,ite_eq_right hz]
    exact tendsto_const_nhds

lemma rowTrace_tendsto {s : ℕ → ℕ → ℕ → ℕ → ℝ} {s₀ : ℕ → ℕ → ℕ → ℝ}
    (hs : ∀ z T p, Tendsto (fun Q => s Q z T p) atTop (𝓝 (s₀ z T p)))
    (r : RowData) (z : ℕ) :
    Tendsto (fun Q => rowTrace (s Q) z r) atTop (𝓝 (rowTrace s₀ z r)) := by
  unfold rowTrace
  apply Tendsto.add
  · apply tendsto_finsetSum
    intro a ha
    exact ((hs _ _ _).const_mul _).mul (hs _ _ _)
  · apply tendsto_finsetSum
    intro a ha
    apply tendsto_finsetSum
    intro b hb
    by_cases he : a.output=b.output
    · simp only [ite_eq_left he]
      exact ((hs _ _ _).const_mul _).mul (hs _ _ _)
    · simp only [ite_eq_right he]
      exact tendsto_const_nhds

lemma rowThreeTrace_tendsto (r : RowData) (z : ℕ) :
    Tendsto (fun Q => rowThreeTrace Q z r) atTop
      (𝓝 (rowTrace threeWeightCoefficientStar z r)) :=
  rowTrace_tendsto threeWeightCoefficient_tendsto r z

lemma threeHighestAverage_eq {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeHighestAverage Q z =
      (1/((2*Q-2)+Q-2*z+1 : ℕ):ℝ) • threeSpinLift hQ hz :=
  threeSpinLift_average_highest hQ hz

lemma three_dimension_identity {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    ((2*Q-2+Q-2*z+1:ℕ):ℝ) / ((2*Q-1:ℕ):ℝ) = threeBodyDimensionRatio Q z := by
  rw [threeBodyDimensionRatio, Nat.cast_add, Nat.cast_sub (by omega : 2*z ≤ 2*Q-2+Q),
      Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2*Q), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
  push_cast
  ring

theorem three_comparison_of_strict_traces {ι : Type*} [Fintype ι]
    (rows : ι → RowData)
    (hc : ∀ z : Fin 16, z.val ≠ 0 → z.val ≠ 1 → z.val ≠ 3 →
      (∑ r, rowTrace threeWeightCoefficientStar z.val (rows r)) <
        (3/2:ℝ) * ((3*(z.val:ℝ)-1)*(-1/2:ℝ)^z.val)) :
    ∀ᶠ Q in atTop, ∀ hQ : 15 ≤ Q,
      ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowThree (by omega) (rows r)) ≤
      ∑ z : Fin 16, threeBodyGramCoefficient Q z.val •
        threeSpinLift (by omega : 2 ≤ Q) (show z.val ≤ Q by omega) := by
  have hseq (z : Fin 16) : ∀ᶠ Q in atTop,
      z.val=0 ∨ z.val=1 ∨ z.val=3 ∨
        (∑ r, rowThreeTrace Q z.val (rows r)) ≤
          threeBodyDimensionRatio Q z.val * threeBodyGramCoefficient Q z.val := by
    by_cases hn : z.val=0 ∨ z.val=1 ∨ z.val=3
    · exact Eventually.of_forall (fun _ => by tauto)
    · have hlim := tendsto_finsetSum Finset.univ (fun r _ => rowThreeTrace_tendsto (rows r) z.val)
      have htarget := (threeBodyDimensionRatio_tendsto z.val).mul
        (threeBodyGramCoefficient_tendsto z.val)
      filter_upwards [hlim.eventually_lt htarget (hc z (by tauto) (by tauto) (by tauto))] with Q hQ
      exact Or.inr (Or.inr (Or.inr hQ.le))
  filter_upwards [eventually_all.mpr hseq] with Q hs
  intro hQ
  simp only [map_sum,rowThree_average hQ,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z hz
  rw [← Finset.sum_smul, threeHighestAverage_eq (by omega) (by omega),smul_smul]
  rcases hs z with hn | hn | hn | he
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inl hn)]
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inr (Or.inl hn))]
  · simp [threeSpinLift_null (by omega : 2 ≤ Q) (by omega : z.val ≤ Q) (Or.inr (Or.inr hn))]
  · apply smul_le_smul_of_nonneg_right _ (threeSpinLift_positive (by omega : 2 ≤ Q) (by omega : z.val ≤ Q)).nonneg
    have hd : (0:ℝ) < ((2*Q-2)+Q-2*z.val+1:ℕ) := by positivity
    have hd₂ : (0:ℝ) < (2*Q-1:ℕ) := by exact_mod_cast (show 0 < 2*Q-1 by omega)
    rw [← three_dimension_identity (by omega : 2 ≤ Q) (by omega : z.val ≤ Q)] at he
    rw [← Finset.mul_sum]
    rw [div_mul_eq_mul_div] at he
    have hh := (le_div_iff₀ hd₂).mp he
    rw [mul_comm _ ((2*Q-1:ℕ):ℝ)] at hh
    rw [mul_comm (↑(2 * Q - 2 + Q - 2 * ↑z + 1) : ℝ)] at hh
    simpa only [div_eq_mul_inv, one_div, one_mul] using (div_le_iff₀ hd).mpr hh

end LaughlinGap.RealOccupation

end

end OAI
