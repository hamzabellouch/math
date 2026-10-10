import OAI.Probability.SATComputability.ObstructionMoment

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable def finiteMap {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (P : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ where
  weight y := P.expect (fun x => if f x = y then 1 else 0)
  nonneg y := P.expect_nonneg (fun x => by split_ifs <;> norm_num)
  total := by
    rw [← FiniteLaw.expect_fintype_sum]
    simp

theorem finiteMap_expect {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (P : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (finiteMap P f).expect g = P.expect (fun x => g (f x)) := by
  simp only [FiniteLaw.expect, finiteMap, Finset.sum_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

noncomputable def unionMaskLaw {n : ℕ}
    (P Q : FiniteLaw (Finset (DeletionCandidate n))) : FiniteLaw (Finset (DeletionCandidate n)) :=
  finiteMap (P.bind (fun _ => Q)) (fun p => p.1 ∪ p.2)

theorem unionMaskLaw_killing {n : ℕ}
    (P Q : FiniteLaw (Finset (DeletionCandidate n))) (U : Finset (DeletionCandidate n)) :
    (unionMaskLaw P Q).expect (fun I => if U ∩ I = ∅ then 1 else 0) =
      P.expect (fun I => if U ∩ I = ∅ then 1 else 0) *
      Q.expect (fun I => if U ∩ I = ∅ then 1 else 0) := by
  rw [unionMaskLaw, finiteMap_expect, FiniteLaw.expect_bind]
  have he (I J : Finset (DeletionCandidate n)) :
      (if U ∩ (I ∪ J) = ∅ then (1 : ℝ) else 0) =
      (if U ∩ I = ∅ then 1 else 0) * (if U ∩ J = ∅ then 1 else 0) := by
    simp only [Finset.inter_union_distrib_left, Finset.union_eq_empty]
    split_ifs <;> simp_all
  simp only [he, FiniteLaw.expect_mul_left, FiniteLaw.expect_mul_right]

noncomputable def catastropheLaw (n : ℕ) (ρ : ℝ≥0) : FiniteLaw (Finset (DeletionCandidate n)) :=
  poissonMixture ρ (fun d => finiteMap (FiniteLaw.uniform : FiniteLaw Unit)
    (fun _ => if d = 0 then Finset.univ else ∅))

theorem catastropheLaw_bound (n : ℕ) (ρ : ℝ≥0) :
    (catastropheLaw n ρ).expect (fun I => if I = Finset.univ then 0 else 1) ≤ ρ := by
  rw [catastropheLaw, poissonMixture_expect]
  simp only [finiteMap_expect, FiniteLaw.expect_const]
  have hi : Integrable (fun d : ℕ =>
      if (if d = 0 then (Finset.univ : Finset (DeletionCandidate n)) else ∅) = Finset.univ
        then (0 : ℝ) else 1) (poissonMeasure ρ) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with d
    split_ifs <;> norm_num
  apply (integral_mono hi (poisson_integrable_count ρ) (fun d => ?_)).trans_eq (poisson_mean ρ)
  by_cases hd : d = 0
  · simp [hd]
  · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    split_ifs <;> linarith

noncomputable def incidentSignLaw {n : ℕ} [NeZero n] (ρ : ℝ≥0) :
    FiniteLaw (Finset (DeletionCandidate n)) :=
  finiteMap ((candidateBlock 60 2 Finset.univ).bind (fun _ => catastropheLaw n ρ))
    (fun p => p.1 ∩ p.2)

theorem incidentSignLaw_killing {n : ℕ} [NeZero n] (ρ : ℝ≥0)
    (U : Finset (DeletionCandidate n)) :
    (incidentSignLaw ρ).expect (fun I => if U ∩ I = ∅ then 1 else 0) ≤
      poissonKillProbability U 2 60 + ρ := by
  rw [incidentSignLaw, finiteMap_expect, FiniteLaw.expect_bind]
  have hb (I J : Finset (DeletionCandidate n)) :
      (if U ∩ (I ∩ J) = ∅ then (1 : ℝ) else 0) ≤
      (if U ∩ I = ∅ then 1 else 0) + (if J = Finset.univ then 0 else 1) := by
    by_cases hJ : J = Finset.univ
    · simp [hJ]
    · split_ifs <;> norm_num
  have h := (candidateBlock (n := n) 60 2 Finset.univ).expect_mono (fun I =>
    (catastropheLaw n ρ).expect_mono (hb I))
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_const] at h
  have he : (candidateBlock 60 2 (Finset.univ : Finset (DeletionCandidate n))).expect
      (fun I => if U ∩ I = ∅ then 1 else 0) = poissonKillProbability U 2 60 := by
    rw [candidateBlock_mask 60 2 U (fun V => if V = ∅ then 1 else 0), candidateBlock_kill]
  rw [he] at h
  exact h.trans (add_le_add le_rfl (catastropheLaw_bound n ρ))

noncomputable def dominatingIncidentLaw {n : ℕ} [NeZero n] (ρ : ℝ≥0) :
    FiniteLaw (Finset (DeletionCandidate n)) := unionMaskLaw (incidentSignLaw ρ) (incidentSignLaw ρ)

theorem dominatingIncidentLaw_killing {n : ℕ} [NeZero n] (ρ : ℝ≥0)
    (U : Finset (DeletionCandidate n)) :
    (dominatingIncidentLaw ρ).expect (fun I => if U.Nonempty ∧ U ∩ I = ∅ then 1 else 0) ≤
      (poissonKillProbability U 2 60 + ρ)^2 := by
  by_cases hU : U.Nonempty
  · simp only [hU, true_and, dominatingIncidentLaw, unionMaskLaw_killing]
    rw [← pow_two]
    exact pow_le_pow_left₀ (FiniteLaw.expect_nonneg _ (fun I => by split_ifs <;> norm_num))
      (incidentSignLaw_killing ρ U) 2
  · simp only [hU, false_and, ite_false, FiniteLaw.expect_const]
    exact sq_nonneg _

theorem dominatingIncidentLaw_delay {n : ℕ} [NeZero n]
    (r : ℝ≥0) (hr : (1 : ℝ)/8 ≤ r) (M : ℕ) (ρ : ℝ≥0)
    (U : Finset (DeletionCandidate n)) :
    (dominatingIncidentLaw ρ).expect (fun I => maskDelayMoment r 3 M U I) ≤
      (48/5 : ℝ) * (∑' j, dyadicMomentCoefficient j) +
      (12/5 : ℝ)*(ρ : ℝ)^2*(M : ℝ)^(6/5 : ℝ) :=
  maskDelayMoment_of_obstruction r hr M (dominatingIncidentLaw ρ) ρ
    (dominatingIncidentLaw_killing ρ) U

end FixedClauseThreshold.Computability

end OAI
