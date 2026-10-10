import OAI.Probability.SATComputability.DyadicMoment

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory
open scoped BigOperators Classical NNReal

theorem poissonKillProbability_nonneg {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k : ℕ) (r : ℝ≥0) :
    0 ≤ poissonKillProbability U k r :=
  integral_nonneg (fun d => batchKillProbability_nonneg U k d)

noncomputable def dyadicIndex {n : ℕ} [NeZero n] (U : Finset (DeletionCandidate n)) : ℕ :=
  if h : U.Nonempty ∧ 0 < poissonKillProbability U 2 60 then
    Nat.find (positive_killing_in_dyadic_bin U h.1 h.2) else 0

theorem dyadicIndex_spec {n : ℕ} [NeZero n] (U : Finset (DeletionCandidate n))
    (h : U.Nonempty ∧ 0 < poissonKillProbability U 2 60) : dyadicBin (dyadicIndex U) U := by
  simp only [dyadicIndex, dite_eq_left h]
  exact Nat.find_spec (positive_killing_in_dyadic_bin U h.1 h.2)

noncomputable def dyadicCapBound {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) : ℝ :=
  if U.Nonempty ∧ 0 < poissonKillProbability U 2 60 then
    min ((M : ℝ)^(1/5 : ℝ)) (dyadicLifetimeBound (dyadicIndex U))
  else (M : ℝ)^(1/5 : ℝ)

theorem dyadicCapBound_nonneg {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) : 0 ≤ dyadicCapBound M U := by
  unfold dyadicCapBound
  split_ifs
  · exact le_min (by positivity) (dyadicLifetimeBound_nonneg _)
  · positivity

theorem dyadicCapBound_le_cap {n : ℕ} [NeZero n]
    (M : ℕ) (U : Finset (DeletionCandidate n)) :
    dyadicCapBound M U ≤ (M : ℝ)^(1/5 : ℝ) := by
  unfold dyadicCapBound
  split_ifs
  · exact min_le_left _ _
  · rfl

theorem dyadicCapBound_controls {n : ℕ} [NeZero n] (r : ℝ≥0)
    (hr : (1 : ℝ)/8 ≤ r) (m M : ℕ) (hm : m ≤ M)
    (U : Finset (DeletionCandidate n)) :
    (FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r 3 Finset.univ)).expect
      (fun xs => (maskLifetime m U xs)^(1/5 : ℝ)) ≤ dyadicCapBound M U := by
  have hc := capped_lifetime_fractional_bound r 3 m M hm U
  unfold dyadicCapBound
  split_ifs with h
  · exact le_min hc (dyadic_lifetime_bound r hr m _ U (dyadicIndex_spec U h))
  · exact hc

theorem dyadicCapBound_weighted {n : ℕ} [NeZero n]
    (M J : ℕ) (U : Finset (DeletionCandidate n))
    (hJ : dyadicIndex U < J) (hU : U.Nonempty) :
    (poissonKillProbability U 2 60)^2 * dyadicCapBound M U ≤
      ∑ j ∈ Finset.range J, if dyadicBin j U then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0 := by
  have hn : ∀ j, 0 ≤ if dyadicBin j U then
      4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0 := by
    intro j
    split_ifs <;> positivity [dyadicLifetimeBound_nonneg j]
  by_cases hp : 0 < poissonKillProbability U 2 60
  · have hb := dyadicIndex_spec U ⟨hU,hp⟩
    have hR : dyadicCapBound M U ≤ dyadicLifetimeBound (dyadicIndex U) := by
      simp only [dyadicCapBound, ite_eq_left (And.intro hU hp)]
      exact min_le_right _ _
    have hq : (poissonKillProbability U 2 60)^2 ≤ 4*(dyadicLevel (dyadicIndex U))^2 := by
      have hqp := dyadicLevel_pos (dyadicIndex U)
      nlinarith [hb.2.2]
    calc
      _ ≤ 4*(dyadicLevel (dyadicIndex U))^2 * dyadicLifetimeBound (dyadicIndex U) :=
        mul_le_mul hq hR (dyadicCapBound_nonneg M U) (by positivity)
      _ = (if dyadicBin (dyadicIndex U) U then
          4*(dyadicLevel (dyadicIndex U))^2*dyadicLifetimeBound (dyadicIndex U) else 0) :=
        (ite_eq_left hb).symm
      _ ≤ _ := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_range.mpr hJ)
  · have hz : poissonKillProbability U 2 60 = 0 :=
      le_antisymm (le_of_not_gt hp) (poissonKillProbability_nonneg U 2 60)
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact Finset.sum_nonneg (fun j _ => hn j)

theorem obstruction_cost_bound {n : ℕ} [NeZero n]
    (P : FiniteLaw (Finset (DeletionCandidate n))) (M J : ℕ) (ε : ℝ)
    (U : Finset (DeletionCandidate n)) (hJ : dyadicIndex U < J)
    (hP : P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
      (poissonKillProbability U 2 60 + ε)^2) :
    (6/5 : ℝ) * P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) *
      dyadicCapBound M U ≤
      (12/5 : ℝ) * (∑ j ∈ Finset.range J, if dyadicBin j U then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0) +
      (12/5 : ℝ)*ε^2*(M : ℝ)^(1/5 : ℝ) := by
  by_cases hU : U.Nonempty
  · have hq := dyadicCapBound_weighted M J U hJ hU
    have he := mul_le_mul_of_nonneg_left (dyadicCapBound_le_cap M U) (sq_nonneg ε)
    have hs : (poissonKillProbability U 2 60 + ε)^2 ≤
        2*(poissonKillProbability U 2 60)^2 + 2*ε^2 := by
      nlinarith [sq_nonneg (poissonKillProbability U 2 60 - ε)]
    have hb := mul_le_mul_of_nonneg_right (hP.trans hs) (dyadicCapBound_nonneg M U)
    nlinarith
  · simp only [hU, false_and, ite_false, FiniteLaw.expect_const, mul_zero, zero_mul]
    apply add_nonneg
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity [dyadicLifetimeBound_nonneg j])
    · positivity

theorem dyadic_bin_cost_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r) (j M : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect
      (fun V => if dyadicBin j V then
        4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0)) ≤
      4*dyadicMomentCoefficient j := by
  let A : ℝ := 4*(dyadicBlock j : ℝ)/dyadicLevel j
  have hA : 0 < A := by
    dsimp [A, dyadicBlock, dyadicTruncation]
    positivity [dyadicLevel_pos j, dyadic_multiplicity_pos j]
  have he (V : Finset (DeletionCandidate n)) :
      (if dyadicBin j V then 4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0) =
      (4*(dyadicLevel j)^2*dyadicLifetimeBound j) * (if dyadicBin j V then 1 else 0) := by
    split_ifs <;> simp
  simp_rw [he, FiniteLaw.expect_mul_left]
  rw [← Finset.mul_sum]
  have ho := mul_le_mul_of_nonneg_left (dyadic_bin_occupation r hr j M U)
    (show 0 ≤ 4*(dyadicLevel j)^2*dyadicLifetimeBound j by
      positivity [dyadicLifetimeBound_nonneg j])
  apply ho.trans_eq
  have hp : A^(6/5 : ℝ) = A^(1/5 : ℝ)*A := by
    have h := Real.rpow_add hA (1/5 : ℝ) 1
    norm_num at h
    exact h
  change (4*(dyadicLevel j)^2*A^(1/5 : ℝ))*A = 4*((dyadicLevel j)^2*A^(6/5 : ℝ))
  rw [hp]
  ring

theorem maskDelayMoment_of_obstruction {n : ℕ} [NeZero n]
    (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r) (M : ℕ)
    (P : FiniteLaw (Finset (DeletionCandidate n))) (ε : ℝ)
    (hP : ∀ U, P.expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
      (poissonKillProbability U 2 60 + ε)^2)
    (U : Finset (DeletionCandidate n)) :
    P.expect (fun I => maskDelayMoment r 3 M U I) ≤
      (48/5 : ℝ) * (∑' j, dyadicMomentCoefficient j) +
      (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
  let J := (Finset.univ.sup (fun V : Finset (DeletionCandidate n) => dyadicIndex V))+1
  have hJ (V : Finset (DeletionCandidate n)) : dyadicIndex V < J := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun V : Finset (DeletionCandidate n) =>
      dyadicIndex V) (Finset.mem_univ V))
  let c : ℕ → Finset (DeletionCandidate n) → ℝ := fun j V =>
    if dyadicBin j V then 4*(dyadicLevel j)^2*dyadicLifetimeBound j else 0
  let B : ℝ := (12/5 : ℝ)*ε^2*(M : ℝ)^(1/5 : ℝ)
  have ho := maskDelayMoment_occupation r 3 M P (dyadicCapBound M)
    (fun m hm V => dyadicCapBound_controls r hr (m+1) M (by omega) V) U
  have hc (V : Finset (DeletionCandidate n)) :
      (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) *
        dyadicCapBound M V ≤ (12/5 : ℝ)*(∑ j ∈ Finset.range J, c j V)+B :=
    obstruction_cost_bound P M J ε V (hJ V) (hP V)
  apply ho.trans
  calc
    _ ≤ ∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect
        (fun V => (12/5 : ℝ)*(∑ j ∈ Finset.range J, c j V)+B) :=
      Finset.sum_le_sum (fun t _ => FiniteLaw.expect_mono _ hc)
    _ = (12/5 : ℝ)*(∑ j ∈ Finset.range J,
        ∑ t ∈ Finset.range M, (candidateBlock (r*t) 3 U).expect (c j)) + (M : ℝ)*B := by
      simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul_left, FiniteLaw.expect_sum,
        FiniteLaw.expect_const, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (12/5 : ℝ)*(∑ j ∈ Finset.range J, 4*dyadicMomentCoefficient j) + (M : ℝ)*B := by
      gcongr with j hj
      exact dyadic_bin_cost_occupation r hr j M U
    _ ≤ (48/5 : ℝ)*(∑' j, dyadicMomentCoefficient j) + (12/5 : ℝ)*ε^2*(M : ℝ)^(6/5 : ℝ) := by
      have hs := dyadicMomentCoefficient_summable.sum_le_tsum (Finset.range J)
        (fun j _ => dyadicMomentCoefficient_nonneg j)
      rw [← Finset.mul_sum]
      have hp : (M : ℝ)*(M : ℝ)^(1/5 : ℝ) = (M : ℝ)^(6/5 : ℝ) := by
        by_cases hM : M = 0
        · subst M
          norm_num
        · have h := (Real.rpow_add (by positivity : (0 : ℝ) < M) 1 (1/5 : ℝ)).symm
          norm_num at h
          exact h
      dsimp only [B]
      nlinarith

end FixedClauseThreshold.Computability

end OAI
