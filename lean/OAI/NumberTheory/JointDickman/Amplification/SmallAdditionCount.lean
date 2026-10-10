import OAI.NumberTheory.JointDickman.Amplification.RegularAlternatives

namespace OAI

/-! # The small-addition contribution to representation multiplicity -/

namespace JointDickman
open Finset Classical Filter
open scoped Topology

noncomputable def highOmissionExponent (τ : ℝ) : ℝ :=
  (1/2+τ)*Real.binEntropy (4*τ/(1/2+τ))

theorem highOmissionExponent_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ 1/100) :
    0 ≤ highOmissionExponent τ := by
  have hd : 0 < (1/2 : ℝ)+τ := by linarith
  apply mul_nonneg (by linarith) (Real.binEntropy_nonneg (div_nonneg (by linarith) hd.le) ?_)
  exact (div_le_one hd).mpr (by linarith)

theorem highOmissionExponent_tendsto :
    Tendsto highOmissionExponent (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt highOmissionExponent 0 := by
    unfold highOmissionExponent
    apply ContinuousAt.mul (by fun_prop)
    apply Real.binEntropy_continuous.continuousAt.comp
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  simpa [highOmissionExponent] using hc.tendsto

theorem regularSmallAlternatives_exp_bound {B L k : ℕ} {τ C : ℝ}
    (A R : Finset ℕ) (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hR : RegularPrimeSet B L τ C R) :
    ((regularSmallAlternatives B L k τ C A R).card : ℝ) ≤
      Real.exp (((((k : ℝ)/L+2*τ)*Real.log 2)+highOmissionExponent τ)*auxiliaryLogLength B) := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  have hQA : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hQR : R ∩ Q = primePrefix B ((k : ℝ)/L) R := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_right]
  have he : Q = (A ∩ Q) ∪ (R ∩ Q) := by
    have hsub : Q ⊆ A ∪ R := by
      dsimp [Q,primePrefix]
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    rw [← union_inter_distrib_right,inter_eq_right.mpr hsub]
  have hQ : (Q.card : ℝ) ≤ ((k : ℝ)/L+2*τ)*auxiliaryLogLength B := by
    have hh : (Q.card : ℝ) ≤ ((A ∩ Q).card : ℝ)+(R ∩ Q).card := by
      have hc : ((A ∩ Q ∪ R ∩ Q).card : ℝ) ≤ (A ∩ Q).card+(R ∩ Q).card := by
        exact_mod_cast card_union_le (A ∩ Q) (R ∩ Q)
      rwa [← he] at hc
    rw [hQA,hQR] at hh
    have ha := (hA.1 k hk).2
    have hr := (hR.1 k hk).2
    nlinarith
  have hcount : ((regularSmallAlternatives B L k τ C A R).card : ℝ) ≤
      (2 : ℝ)^Q.card*
        (((A \ Q).powerset.filter (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card : ℝ) := by
    exact_mod_cast regularSmallAlternatives_count A R hL hk hA
  have hregion : ((A \ Q).card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B :=
    (show ((A \ Q).card : ℝ) ≤ A.card by
      exact_mod_cast card_le_card (show A \ Q ⊆ A from sdiff_subset)).trans (hA.total_upper hL)
  have homit := high_omission_count_bound (A \ Q) hτ hτsmall hℓ hregion
  have hp : (2 : ℝ)^Q.card ≤ Real.exp ((((k : ℝ)/L+2*τ)*auxiliaryLogLength B)*Real.log 2) := by
    calc
      _ = Real.exp ((Q.card : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hQ (Real.log_nonneg (by norm_num)))
  refine hcount.trans ((mul_le_mul hp homit (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  dsimp [highOmissionExponent]
  ring

end JointDickman

end OAI
