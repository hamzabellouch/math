import OAI.Probability.SATComputability.MaskLifetime

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory
open scoped BigOperators Classical NNReal

theorem sixth_fifth_increment {x : ℝ} (hx : 0 ≤ x) :
    (x+1)^(6/5 : ℝ) - x^(6/5 : ℝ) ≤
      (6/5 : ℝ) * (x+1)^(1/5 : ℝ) := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (show x ≤ x+1 by linarith)
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1/5))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (x+1)^(1/5 : ℝ))
      volume x (x+1))
    (fun y hy => Real.rpow_le_rpow (hx.trans hy.1) hy.2 (by norm_num : (0 : ℝ) ≤ 1/5))
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1/5)),
    intervalIntegral.integral_const] at h
  norm_num at h
  nlinarith

theorem maskLifetime_mono {n m : ℕ} {U V : Finset (DeletionCandidate n)}
    (hUV : U ⊆ V) (xs : Fin m → Finset (DeletionCandidate n)) :
    maskLifetime m U xs ≤ maskLifetime m V xs := by
  induction m generalizing U V with
  | zero => exact le_rfl
  | succ m ih =>
    exact add_le_add (candidateAlive_mono hUV)
      (ih (Finset.inter_subset_inter_right hUV) (Fin.tail xs))

theorem maskLifetime_empty {n m : ℕ}
    (xs : Fin m → Finset (DeletionCandidate n)) : maskLifetime m ∅ xs = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [maskLifetime, candidateAlive, ih]

noncomputable def maskDelayMoment {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k m : ℕ) (U I : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin m => candidateBlock r k Finset.univ)).expect
    (fun xs => (maskLifetime m U xs - maskLifetime m (U ∩ I) xs)^(6/5 : ℝ))

theorem maskDelayMoment_zero {n : ℕ} [NeZero n] (r : ℝ≥0) (k : ℕ)
    (U I : Finset (DeletionCandidate n)) : maskDelayMoment r k 0 U I = 0 := by
  simp [maskDelayMoment, maskLifetime]

theorem maskDelayMoment_step {n : ℕ} [NeZero n] (r : ℝ≥0) (k m : ℕ)
    (U I : Finset (DeletionCandidate n)) :
    maskDelayMoment r k (m+1) U I ≤
      (candidateBlock r k U).expect (fun V => maskDelayMoment r k m V I) +
      if U.Nonempty ∧ U ∩ I = ∅ then
        (6/5 : ℝ) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) U xs)^(1/5 : ℝ))
      else 0 := by
  let P := FiniteLaw.pi (fun _ : Fin m => candidateBlock (n := n) r k Finset.univ)
  have he : (candidateBlock r k Finset.univ).expect (fun V =>
      P.expect (fun xs => (maskLifetime m (U ∩ V) xs -
        maskLifetime m ((U ∩ V) ∩ I) xs)^(6/5 : ℝ))) =
      (candidateBlock r k U).expect (fun V => maskDelayMoment r k m V I) := by
    simpa only [maskDelayMoment, P] using
      candidateBlock_mask r k U (fun V => maskDelayMoment r k m V I)
  unfold maskDelayMoment
  rw [FiniteLaw.expect_pi_cons]
  by_cases h : U.Nonempty ∧ U ∩ I = ∅
  · rw [ite_eq_left h]
    rw [FiniteLaw.expect_pi_cons]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons]
    have hpoint (V : Finset (DeletionCandidate n)) (xs : Fin m → Finset (DeletionCandidate n)) :
        (candidateAlive U + maskLifetime m (U ∩ V) xs -
          (candidateAlive (U ∩ I) + maskLifetime m ((U ∩ I) ∩ V) xs))^(6/5 : ℝ) ≤
        (maskLifetime m (U ∩ V) xs - maskLifetime m ((U ∩ V) ∩ I) xs)^(6/5 : ℝ) +
          (6/5 : ℝ) * (candidateAlive U + maskLifetime m (U ∩ V) xs)^(1/5 : ℝ) := by
      simp only [h.2, Finset.empty_inter, maskLifetime_empty,
        show (U ∩ V) ∩ I = ∅ by rw [Finset.inter_right_comm, h.2, Finset.empty_inter],
        candidateAlive, ite_eq_left h.1, Finset.not_nonempty_empty, ite_false, zero_add, sub_zero]
      have hi := sixth_fifth_increment (maskLifetime_nonneg (U ∩ V) xs)
      simpa only [add_comm] using (sub_le_iff_le_add.mp hi)
    have hb := (candidateBlock r k Finset.univ).expect_mono (fun V =>
      P.expect_mono (hpoint V))
    simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul_left] at hb
    rw [he] at hb
    exact hb
  · rw [ite_eq_right h, add_zero]
    have halive : candidateAlive U = candidateAlive (U ∩ I) := by
      by_cases hU : U.Nonempty
      · have hI : (U ∩ I).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun he => h ⟨hU, he⟩)
        simp [candidateAlive, hU, hI]
      · have hI : ¬ (U ∩ I).Nonempty := fun hi => hU (hi.mono Finset.inter_subset_left)
        simp [candidateAlive, hU, hI]
    simp only [maskLifetime, Fin.cons_zero, Fin.tail_cons, halive, add_sub_add_left_eq_sub]
    simpa only [Finset.inter_right_comm, P, maskDelayMoment] using le_of_eq he

theorem finite_expect_comm {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Ξ) (f : Ω → Ξ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem finiteKernel_accumulation {Ω : Type*} [Fintype Ω]
    (K : Ω → FiniteLaw Ω) (g : ℕ → Ω → ℝ) (cost : Ω → ℝ) (M : ℕ)
    (hzero : ∀ x, g 0 x ≤ 0)
    (hstep : ∀ m < M, ∀ x, g (m+1) x ≤ (K x).expect (g m) + cost x) (x : Ω) :
    g M x ≤ ∑ t ∈ Finset.range M, (finiteKernelStep K)^[t] cost x := by
  have hi (m : ℕ) (hm : m ≤ M) :
      ∀ y, g m y ≤ ∑ t ∈ Finset.range m, (finiteKernelStep K)^[t] cost y := by
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      intro y
      apply (hstep m (by omega) y).trans
      have hb := (K y).expect_mono (ih (by omega))
      apply (add_le_add hb le_rfl).trans_eq
      rw [FiniteLaw.expect_sum, Finset.sum_range_succ']
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply']
      rfl
  exact hi M le_rfl x

theorem maskDelayMoment_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k M : ℕ) (P : FiniteLaw (Finset (DeletionCandidate n)))
    (bound : Finset (DeletionCandidate n) → ℝ)
    (hbound : ∀ m < M, ∀ U,
      (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
        (fun xs => (maskLifetime (m+1) U xs)^(1/5 : ℝ)) ≤ bound U)
    (U : Finset (DeletionCandidate n)) :
    P.expect (fun I => maskDelayMoment r k M U I) ≤
      ∑ t ∈ Finset.range M, (candidateBlock (r*t) k U).expect (fun V =>
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * bound V) := by
  let cost := fun V => (6/5 : ℝ) *
    P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * bound V
  have hs (m : ℕ) (hm : m < M) (V : Finset (DeletionCandidate n)) :
      P.expect (fun I => maskDelayMoment r k (m+1) V I) ≤
        (candidateBlock r k V).expect (fun W => P.expect (fun I => maskDelayMoment r k m W I)) + cost V := by
    have hi := P.expect_mono (fun I => maskDelayMoment_step r k m V I)
    rw [FiniteLaw.expect_add, finite_expect_comm] at hi
    apply hi.trans
    apply add_le_add le_rfl
    have he : P.expect (fun I =>
        if V.Nonempty ∧ V ∩ I = ∅ then (6/5 : ℝ) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ)) else 0) =
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) *
          (FiniteLaw.pi (fun _ : Fin (m+1) => candidateBlock (n := n) r k Finset.univ)).expect
            (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ)) := by
      let z := (FiniteLaw.pi (fun _ : Fin (m+1) =>
        candidateBlock (n := n) r k Finset.univ)).expect
          (fun xs => (maskLifetime (m+1) V xs)^(1/5 : ℝ))
      change P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then (6/5 : ℝ)*z else 0) =
        (6/5 : ℝ) * P.expect (fun I => if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * z
      calc
        _ = P.expect (fun I => (if V.Nonempty ∧ V ∩ I = ∅ then 1 else 0) * ((6/5 : ℝ)*z)) := by
          apply P.expect_congr
          intro I
          split_ifs <;> simp
        _ = _ := by rw [FiniteLaw.expect_mul_right]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (hbound m hm V)
      (mul_nonneg (by norm_num) (P.expect_nonneg (fun I => by split_ifs <;> norm_num)))
  have hz : ∀ V, P.expect (fun I => maskDelayMoment r k 0 V I) ≤ 0 := by
    intro V
    simp only [maskDelayMoment_zero, FiniteLaw.expect_const, le_refl]
  have h := finiteKernel_accumulation (candidateBlock r k)
    (fun m V => P.expect (fun I => maskDelayMoment r k m V I)) cost M hz hs U
  change P.expect (fun I => maskDelayMoment r k M U I) ≤
    ∑ t ∈ Finset.range M, (poissonCandidateStep r k)^[t] cost U at h
  simpa only [poissonCandidateStep_iterate, cost] using h

end FixedClauseThreshold.Computability

end OAI
