import OAI.Probability.ThorpShuffle.MaskedResampling

namespace OAI

universe uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

@[simp] theorem run_snoc (d t : ℕ) (ω : History d t) (c : Coins d) :
    run d (t + 1) (Fin.snoc ω c) = step d c * run d t ω := by
  rw [run_succ]
  simp

theorem flow_joint_identity {ι : Type uι} (d : ℕ) (v : RawState (d + 1))
    (e : ι → Position (d + 1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      ∑ x, v.weight x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (rawIterate d v t ω).weight y * f ((run (d + 1) t ω) ∘ e) y) := by
  induction t generalizing f with
  | zero => simp only [run_zero, rawIterate]; rfl
  | succ t ih =>
    let F (e' : ι → Position (d + 1)) (x : Position (d + 1)) : ℝ :=
      mean (fun c : Coins (d + 1) => f ((step (d + 1) c) ∘ e') (step (d + 1) c x))
    have hleft :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ x, v.weight x * f ((run (d + 1) (t + 1) ω) ∘ e) (run (d + 1) (t + 1) ω x)) =
        mean (fun ω : History (d + 1) t =>
          ∑ x, v.weight x * F ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [run_snoc]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      rfl
    have hright :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ y, (rawIterate d v (t + 1) ω).weight y * f ((run (d + 1) (t + 1) ω) ∘ e) y) =
        mean (fun ω : History (d + 1) t =>
          ∑ y, (rawIterate d v t ω).weight y * F ((run (d + 1) t ω) ∘ e) y) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [run_snoc, rawIterate_snoc]
      change mean (fun c : Position d → Bool =>
        ∑ y, physicalFlow d (rawIterate d v t ω).free (rawIterate d v t ω).weight c y *
          f ((step (d + 1) c) ∘ ((run (d + 1) t ω) ∘ e)) y) = _
      rw [physicalFlow_joint d (rawIterate d v t ω).free (rawIterate d v t ω).weight
        ((run (d + 1) t ω) ∘ e) (by
          intro i
          simp only [Function.comp_apply, rawIterate_free, Equiv.symm_apply_apply]
          exact he i)]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      rfl
    exact hleft.trans ((ih F).trans hright.symm)

theorem centered_joint_identity {ι : Type uι} (d : ℕ) (v : CenteredState (d + 1))
    (e : ι → Position (d + 1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      ∑ x, v.weight x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (iterateState d v t ω).weight y * f ((run (d + 1) t ω) ∘ e) y) := by
  have hh := flow_joint_identity d v.raw e he t f
  simp_rw [← iterateState_raw] at hh
  exact hh

theorem centeredPoint_test {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (f : α → ℝ) :
    (∑ x, centeredPoint B tag x * f x) =
      f tag - (1 / (freeCount B : ℝ)) * (∑ x, if B x then f x else 0) := by
  simp only [centeredPoint, sub_mul, mul_assoc, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  simp

theorem tagged_deviation_identity {ι : Type uι} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (iterateState d (initialState (d + 1) B tag ht) t ω).weight y *
        f ((run (d + 1) t ω) ∘ e) y) := by
  rw [← centered_joint_identity d (initialState (d + 1) B tag ht) e he t f]
  apply mean_congr
  intro ω
  change _ = ∑ x, centeredPoint B tag x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)
  rw [centeredPoint_test]
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp (run (d + 1) t ω)
      (fun y => if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0)).symm

end Conditional

end Thorp

end

end OAI
