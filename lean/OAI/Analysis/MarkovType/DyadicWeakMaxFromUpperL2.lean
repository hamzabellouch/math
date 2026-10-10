import OAI.Analysis.MarkovType.FiniteBoundedEnergyScale
import OAI.Analysis.MarkovType.FiniteTruncationTail
import OAI.Analysis.MarkovType.DyadicWeakMaxDefinition
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dyadicDifference_norm_predictable {N : ℕ} (φ : DyadicAtom N → E)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (dyadicFiltration N).AdaptedAt (n - 1)
      (fun ω => ‖finiteDifference (dyadicProcess φ) n ω‖) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      have hnN' : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hnN
      have hd : finiteDifference (dyadicProcess φ) (n + 1) =
          dyadicIncrement φ (⟨n, hnN'⟩ : Fin N) := by
        funext ω
        rw [dyadicProcess_difference_succ, dite_eq_left hnN']
      simp only [Nat.add_sub_cancel, hd]
      intro ω η hωη
      exact dyadicIncrement_norm_predictable φ (⟨n, hnN'⟩ : Fin N) hωη

theorem dyadicDifference_expected_cost {N : ℕ} (φ : DyadicAtom N → E) (a : ℝ) :
    (dyadicLaw N).expect
      (cumulativeCost (fun n ω => ‖finiteDifference (dyadicProcess φ) n ω‖ ^ a) N) =
      ∑ j : Fin N, finiteMoment (dyadicLaw N).mass a (dyadicIncrement φ j) := by
  classical
  unfold FiniteLaw.expect cumulativeCost
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  unfold finiteMoment
  apply Finset.sum_congr rfl
  intro ω _
  rw [dyadicProcess_difference_succ, dite_eq_left j.is_lt]

theorem dyadicProcess_eq_partialSum_of_root_zero {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) :
    dyadicProcess φ = partialSumProcess (finiteDifference (dyadicProcess φ)) := by
  funext n ω
  simpa only [dyadicProcess_zero, hroot, zero_add, partialSumProcess] using
    finiteDifference_telescope (dyadicProcess φ) n ω

theorem finiteUpperL2_normalizedWeakMax {a r χ : ℝ}
    (ha : 1 < a) (har : a < r) (hr2 : r ≤ 2) (hχ : 0 ≤ χ)
    (hUpper : FiniteUpperL2 E r χ) :
    DyadicNormalizedWeakMax E a (1 + (boundedEnergyConstant a r χ) ^ (2 : ℕ)) := by
  intro N φ hroot hinput t ht
  let d := finiteDifference (dyadicProcess φ)
  have hM := dyadicProcess_isMartingale φ N
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hadapt : ∀ n, 0 < n → n ≤ N → (dyadicFiltration N).AdaptedAt n (d n) :=
    fun n _ hnN => hM.difference_adapted hnN
  have hzero : ∀ n, 0 < n → n ≤ N →
      HasZeroConditionalSum (dyadicLaw N) ((dyadicFiltration N).part (n - 1)) (d n) :=
    hM.2
  have hnorm : ∀ n, 0 < n → n ≤ N →
      (dyadicFiltration N).AdaptedAt (n - 1) (fun ω => ‖d n ω‖) :=
    dyadicDifference_norm_predictable φ
  have henergy : (dyadicLaw N).expect (cumulativeCost (fun n ω => ‖d n ω‖ ^ a) N) ≤ 1 := by
    change (dyadicLaw N).expect
      (cumulativeCost (fun n ω => ‖finiteDifference (dyadicProcess φ) n ω‖ ^ a) N) ≤ 1
    rw [dyadicDifference_expected_cost]
    have hid := dyadicInputMoment φ a
    have hroot_nonneg : 0 ≤ ‖dyadicRoot φ‖ ^ a := Real.rpow_nonneg (norm_nonneg _) _
    linarith
  have hBound (s : ℝ) (hs : 0 < s) :
      finiteL2Norm (dyadicLaw N) (partialSumProcess (fun n ω =>
        budgetCoefficient (fun k η => ‖d k η‖ ^ a) (s ^ a) n ω • d n ω) N) ≤
          boundedEnergyConstant a r χ * s :=
    finiteUpperL2_budget_L2 ha0 har hχ hs hUpper (dyadicLaw N) (dyadicFiltration N)
      d N hadapt hzero hnorm
  have h := finite_budget_truncation_tail (dyadicLaw N) (dyadicFiltration N) d N
    ha (har.le.trans hr2) (boundedEnergyConstant_nonneg ha0 har hχ)
    hadapt hzero hnorm henergy hBound ht
  simpa only [d, ← dyadicProcess_eq_partialSum_of_root_zero φ hroot] using h

end MarkovSuperreflexivity

end

end OAI
