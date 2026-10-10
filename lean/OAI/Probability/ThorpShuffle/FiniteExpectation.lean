import OAI.Probability.ThorpShuffle.ConditionalFlow

namespace OAI

universe uΩ uι uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_congr {Ω : Type uΩ} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

theorem mean_zero {Ω : Type uΩ} [Fintype Ω] : mean (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [mean]

theorem mean_const {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    mean (fun _ : Ω => a) = a := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hc]

theorem mean_add {Ω : Type uΩ} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul_const {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => f ω * a) = mean f * a := by
  simp only [mean, ← Finset.sum_mul]
  ring

theorem mean_const_mul {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => a * f ω) = a * mean f := by
  simpa only [mul_comm] using mean_mul_const f a

theorem mean_sum {Ω : Type uΩ} {ι : Type uι} [Fintype Ω] (s : Finset ι) (f : Ω → ι → ℝ) :
    mean (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, mean (fun ω => f ω i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_nonneg {Ω : Type uΩ} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => hf ω)) (Nat.cast_nonneg _)

theorem mean_le_mean {Ω : Type uΩ} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    mean f ≤ mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_le_const {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω] {f : Ω → ℝ} {a : ℝ}
    (h : ∀ ω, f ω ≤ a) : mean f ≤ a := by
  simpa only [mean_const] using mean_le_mean h

theorem mean_equiv {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : mean (f ∘ e) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem mean_prod {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (f : Ω × Ω' → ℝ) : mean f = mean (fun ω => mean (fun ω' => f (ω, ω'))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem mean_comm {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    mean (fun ω => mean (f ω)) = mean (fun ω' => mean (fun ω => f ω ω')) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem mean_history_succ (d t : ℕ) (f : History d (t + 1) → ℝ) :
    mean f = mean (fun ω : History d t => mean (fun c : Coins d => f (Fin.snoc ω c))) := by
  have h := mean_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins d)) f
  rw [mean_prod] at h
  rw [← h, mean_comm]
  rfl

end Conditional

@[simp] theorem run_zero (d : ℕ) (ω : History d 0) : run d 0 ω = 1 := by
  simp [run]

theorem run_succ (d t : ℕ) (ω : History d (t + 1)) :
    run d (t + 1) ω = step d (ω (Fin.last t)) *
      run d t (fun i => ω i.castSucc) := by
  simp only [run, List.ofFn_succ']
  rw [List.concat_eq_append, List.reverse_concat', List.prod_cons]

namespace Conditional

theorem iterateState_free (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (iterateState d v t ω).free x = v.free ((run (d + 1) t ω).symm x) := by
  induction t generalizing x with
  | zero => simp only [iterateState, run_zero]; rfl
  | succ t ih =>
    change (iterateState d v t (fun i => ω i.castSucc)).free
      ((step (d + 1) (ω (Fin.last t))).symm x) = _
    rw [ih, run_succ]
    rfl

theorem iterateState_freeCount (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) : freeCount (iterateState d v t ω).free = freeCount v.free := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  simp only [iterateState_free]
  exact Equiv.sum_comp (run (d + 1) t ω).symm (fun x => if v.free x then (1 : ℝ) else 0)

theorem expectedEnergy_succ (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedEnergy d v (t + 1) = mean (fun ω : History (d + 1) t =>
      mean (fun c : Coins (d + 1) => ∑ x, (nextState d (iterateState d v t ω) c).weight x ^ 2)) := by
  unfold expectedEnergy
  rw [mean_history_succ]
  apply mean_congr
  intro ω
  apply mean_congr
  intro c
  simp [iterateState]

end Conditional

end Thorp

end

end OAI
