import OAI.Probability.SATComputability.BatchKilling
import OAI.Probability.DilutedSpin.FiniteProducts
import OAI.Probability.DilutedSpin.FiniteProjection

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

noncomputable def candidateResidual {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : Finset (DeletionCandidate n) :=
  U.filter (fun x => ∀ j, ¬∀ l, literalFalse x (cs j l))

def candidateAlive {n : ℕ} (U : Finset (DeletionCandidate n)) : ℝ :=
  if U.Nonempty then 1 else 0

noncomputable def candidateStep {n : ℕ} [NeZero n] (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) : ℝ :=
  (FiniteLaw.uniform : FiniteLaw (Fin k → SignedLiteral n)).expect
    (fun c => f (U.filter (fun x => ¬∀ l, literalFalse x (c l))))

theorem candidateResidual_cons {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (c : Fin k → SignedLiteral n) (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U (Fin.cons c cs) =
      candidateResidual (U.filter (fun x => ¬∀ l, literalFalse x (c l))) cs := by
  ext x
  simp [candidateResidual, Fin.forall_fin_succ, and_assoc]

theorem candidateResidual_empty_iff {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs = ∅ ↔ batchKills U cs := by
  simp only [candidateResidual, Finset.filter_eq_empty_iff, batchKills]
  constructor
  · intro h x hx
    by_contra hn
    apply h hx
    intro j hj
    exact hn ⟨j, hj⟩
  · intro h x hx hn
    obtain ⟨j, hj⟩ := h x hx
    exact hn j hj

theorem candidateStep_mono {n : ℕ} [NeZero n] (k : ℕ) :
    Monotone (candidateStep (n := n) k) := by
  intro f g h U
  exact FiniteLaw.expect_mono _ (fun _ => h _)

theorem candidateStep_add_const {n : ℕ} [NeZero n] (k : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (c : ℝ) :
    candidateStep k (f + fun _ => c) = candidateStep k f + fun _ => c := by
  funext U
  exact (FiniteLaw.expect_add _ _ _).trans (by simp [candidateStep, Pi.add_apply])

theorem candidateStep_comm {n : ℕ} [NeZero n] (k l : ℕ) :
    Function.Commute (candidateStep (n := n) k) (candidateStep l) := by
  intro f
  funext U
  unfold candidateStep
  rw [FiniteLaw.expect_comm]
  apply FiniteLaw.expect_congr
  intro c
  apply FiniteLaw.expect_congr
  intro d
  congr 1
  ext x
  simp only [Finset.mem_filter]
  tauto

theorem candidateStep_iterate {n : ℕ} [NeZero n] (k d : ℕ)
    (f : Finset (DeletionCandidate n) → ℝ) (U : Finset (DeletionCandidate n)) :
    (candidateStep k)^[d] f U =
      (FiniteLaw.uniform : FiniteLaw (Fin d → Fin k → SignedLiteral n)).expect
        (fun cs => f (candidateResidual U cs)) := by
  induction d generalizing U with
  | zero => simp [candidateResidual, FiniteLaw.expect, FiniteLaw.uniform]
  | succ d ih =>
    rw [Function.iterate_succ_apply', candidateStep]
    simp_rw [ih]
    conv_rhs => rw [uniformFiniteLaw_pi, FiniteLaw.expect_pi_cons]
    rw [← uniformFiniteLaw_pi]
    apply FiniteLaw.expect_congr
    intro c
    apply FiniteLaw.expect_congr
    intro cs
    rw [candidateResidual_cons]

theorem candidateKill_iterate {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (k d : ℕ) :
    batchKillProbability U k d = 1 - (candidateStep k)^[d] candidateAlive U := by
  rw [candidateStep_iterate]
  have he (cs : Fin d → Fin k → SignedLiteral n) :
      (if batchKills U cs then (1 : ℝ) else 0) =
        1 - candidateAlive (candidateResidual U cs) := by
    rw [candidateAlive, ← candidateResidual_empty_iff]
    by_cases h : candidateResidual U cs = ∅
    · simp [h]
    · simp [h, Finset.nonempty_iff_ne_empty]
  simp_rw [batchKillProbability, he, FiniteLaw.expect_sub, FiniteLaw.expect_const]

theorem operator_iterate_add_const {X : Type*} (A : (X → ℝ) → X → ℝ)
    (hA : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (m : ℕ) (f : X → ℝ) (c : ℝ) :
    A^[m] (f + fun _ => c) = A^[m] f + fun _ => c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hA, Function.iterate_succ_apply']

theorem operator_replacement {X : Type*} (A B : (X → ℝ) → X → ℝ)
    (hA : Monotone A) (hB : Monotone B)
    (hAc : ∀ f c, A (f + fun _ => c) = A f + fun _ => c)
    (hBc : ∀ f c, B (f + fun _ => c) = B f + fun _ => c)
    (hcomm : Function.Commute A B) (f : X → ℝ) (δ : ℝ)
    (hone : A f ≤ B f + fun _ => δ) (d : ℕ) :
    A^[d] f ≤ B^[d] f + fun _ => (d : ℝ)*δ := by
  induction d with
  | zero => intro x; simp
  | succ d ih =>
    have h₁ := hA.iterate d hone
    rw [operator_iterate_add_const A hAc, hcomm.iterate_left d f] at h₁
    have h₂ := hB ih
    rw [hBc, ← Function.iterate_succ_apply' B d f] at h₂
    intro x
    have h₁x := h₁ x
    have h₂x := h₂ x
    simp only [Pi.add_apply] at h₁x h₂x
    rw [Function.iterate_succ_apply]
    change A^[d] (A f) x ≤ B^[d+1] f x + ((d+1 : ℕ) : ℝ)*δ
    push_cast
    linarith

theorem relaxed_sequential_replacement {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) {d : ℕ} (hd : 0 < d) (L : ℕ) :
    batchKillProbability U 2 L - (L : ℝ)/(d : ℝ)^2 ≤
      batchKillProbability U 3 (L*d) := by
  have hone : (candidateStep (n := n) 3)^[d] candidateAlive ≤
      candidateStep 2 candidateAlive + fun _ => 1/(d : ℝ)^2 := by
    intro V
    by_cases hV : V.Nonempty
    · have h := relaxed_one_replacement hV hd
      have he : batchKillProbability V 2 1 = oneTestKill V 2 := by
        rw [candidateKill_iterate, Function.iterate_one, candidateStep]
        unfold oneTestKill
        rw [← FiniteLaw.expect_const (FiniteLaw.uniform : FiniteLaw (Fin 2 → SignedLiteral n)) 1,
          ← FiniteLaw.expect_sub]
        apply FiniteLaw.expect_congr
        intro c
        have hf : (V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty ↔
            ¬testKills V c := by
          constructor
          · rintro ⟨x, hx⟩ hk
            exact (Finset.mem_filter.mp hx).2 (hk x (Finset.mem_filter.mp hx).1)
          · intro hk
            by_contra he
            apply hk
            intro x hx
            by_contra hh
            exact he ⟨x, Finset.mem_filter.mpr ⟨hx, hh⟩⟩
        simp only [FiniteLaw.expect_const]
        by_cases hc : ∀ x ∈ V, ∀ l, literalFalse x (c l)
        · have he : ¬(V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty :=
            fun hne => (hf.mp hne) hc
          rw [candidateAlive, ite_eq_right he, ite_eq_left hc]
          norm_num
        · have he : (V.filter (fun x => ¬∀ l, literalFalse x (c l))).Nonempty := hf.mpr hc
          rw [candidateAlive, ite_eq_left he, ite_eq_right hc]
          norm_num
      rw [← he, candidateKill_iterate, candidateKill_iterate, Function.iterate_one] at h
      exact (by dsimp only [Pi.add_apply]; linarith)
    · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      subst V
      simp [candidateStep_iterate, candidateStep, candidateResidual, candidateAlive]
  have h := operator_replacement (candidateStep (n := n) 3)^[d] (candidateStep 2)
    ((candidateStep_mono 3).iterate d) (candidateStep_mono 2)
    (operator_iterate_add_const _ (candidateStep_add_const 3) d)
    (candidateStep_add_const 2) ((candidateStep_comm 3 2).iterate_left d)
    candidateAlive (1/(d : ℝ)^2) hone L U
  rw [← Function.iterate_mul, Nat.mul_comm d L] at h
  rw [candidateKill_iterate, candidateKill_iterate]
  simp only [Pi.add_apply, mul_one_div] at h
  linarith

end FixedClauseThreshold.Computability

end OAI
