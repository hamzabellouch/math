import OAI.Analysis.MarkovType.MarkedPaths

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {S E A : Type*} [sectionFintypeS : Fintype S] [sectionFintypeE : Fintype E] [sectionFintypeA : Fintype A]

def markedLetters (mark : E → A) {n : ℕ} (ω : MarkedPath S E n) : Fin n → A :=
  fun i => mark (ω.2 i)

omit sectionFintypeS sectionFintypeE sectionFintypeA in
theorem markedLetters_snoc [Fintype S] [Fintype E] [Fintype A] (mark : E → A) {n : ℕ}
    (ω : MarkedPath S E n) (e : E) :
    markedLetters mark (markedSnoc ω e) = Fin.snoc (markedLetters mark ω) (mark e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [markedLetters, markedSnoc]
  · simp [markedLetters, markedSnoc]

@[simp] theorem markedExpect_const (C : FiniteMarkedChain S E) (n : ℕ) (a : ℝ) :
    markedExpect C n (fun _ => a) = a := by
  simp only [markedExpect, ← Finset.sum_mul, sum_markedPathWeight, one_mul]

theorem sum_outgoing_letter (C : FiniteMarkedChain S E) (mark : E → A)
    (ρ : A → ℝ)
    (hrow : ∀ s a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) = ρ a)
    (s : S) (H : A → ℝ) :
    (∑ e, (if C.src e = s then C.q e else 0) * H (mark e)) =
      ∑ a, ρ a * H a := by
  classical
  calc
    _ = ∑ a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) * H a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hs : C.src e = s <;> simp [hs]
    _ = _ := by simp_rw [hrow]

theorem markedExpect_uniform_letters (C : FiniteMarkedChain S E) (mark : E → A)
    (hrow : ∀ s a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) =
      (Fintype.card A : ℝ)⁻¹)
    (n : ℕ) (F : (Fin n → A) → ℝ) :
    markedExpect C n (fun ω => F (fun i => mark (ω.2 i))) =
      ((Fintype.card A : ℝ)⁻¹) ^ n * ∑ w : Fin n → A, F w := by
  classical
  let c : ℝ := (Fintype.card A : ℝ)⁻¹
  change markedExpect C n (fun ω => F (markedLetters mark ω)) = c ^ n * ∑ w, F w
  induction n with
  | zero =>
      have hw (ω : MarkedPath S E 0) : markedLetters mark ω = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp_rw [hw]
      rw [markedExpect_const]
      simp
      congr 1
  | succ n ih =>
      calc
        _ = ∑ ω : MarkedPath S E n, markedPathWeight C n ω *
            (∑ a : A, c * F (Fin.snoc (markedLetters mark ω) a)) := by
          rw [markedExpect_snoc]
          simp only [markedLetters_snoc, mul_assoc]
          simp_rw [← Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          congr 1
          simpa only [← Finset.mul_sum] using
            sum_outgoing_letter C mark (fun _ => c) hrow
              (markedState C ω (Fin.last n))
              (fun a => F (Fin.snoc (markedLetters mark ω) a))
        _ = ∑ a : A, c * markedExpect C n
            (fun ω => F (Fin.snoc (markedLetters mark ω) a)) := by
          simp only [markedExpect, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ = ∑ a : A, c * (c ^ n * ∑ w : Fin n → A, F (Fin.snoc w a)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [ih (fun w => F (Fin.snoc w a))]
        _ = c ^ (n + 1) * ∑ w : Fin (n + 1) → A, F w := by
          rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp F]
          change (∑ a : A, c * (c ^ n * ∑ w : Fin n → A, F (Fin.snoc w a))) =
            c ^ (n + 1) * ∑ z : A × (Fin n → A), F (Fin.snoc z.2 z.1)
          rw [Fintype.sum_prod_type, pow_succ]
          simp_rw [← mul_assoc, ← Finset.mul_sum]
          ring

theorem markedProb_uniform_letter_word (C : FiniteMarkedChain S E) (mark : E → A)
    (hrow : ∀ s a, (∑ e, if C.src e = s ∧ mark e = a then C.q e else 0) =
      (Fintype.card A : ℝ)⁻¹)
    (n : ℕ) (w : Fin n → A) :
    markedProb C n (fun ω => (fun i => mark (ω.2 i)) = w) =
      ((Fintype.card A : ℝ)⁻¹) ^ n := by
  classical
  let F : (Fin n → A) → ℝ := fun v => if v = w then 1 else 0
  calc
    _ = markedExpect C n (fun ω => F (fun i => mark (ω.2 i))) := by
      unfold markedProb markedExpect
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hw : (fun i => mark (ω.2 i)) = w <;> simp [F, hw]
    _ = ((Fintype.card A : ℝ)⁻¹) ^ n * ∑ v : Fin n → A, F v :=
      markedExpect_uniform_letters C mark hrow n F
    _ = _ := by simp [F]

end MarkovSuperreflexivity

end

end OAI
