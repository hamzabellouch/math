import OAI.Probability.ThorpShuffle.TaggedCompletion

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem prefix_one_step_bound (d t k : ℕ) (e : Fin (k + 1) → Position (d + 1))
    (he : Function.Injective e) (f : (Fin (k + 1) → Position (d + 1)) → ℝ)
    (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 1) t => f ((run (d + 1) t ω) ∘ e)) -
      mean (fun ω : History (d + 1) t => completeTest f ((run (d + 1) t ω) ∘ Fin.init e))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1) (freeOf (Fin.init e)) (e (Fin.last k))
        (by
          apply (freeOf_true _ _).mpr
          intro i hi
          exact Fin.castSucc_ne_last i (he hi))) t) := by
  have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
    apply (freeOf_true _ _).mpr
    intro i hi
    exact Fin.castSucc_ne_last i (he hi)
  have hh := tagged_deviation_bound d (freeOf (Fin.init e)) (e (Fin.last k)) ht
    (Fin.init e) (freeOf_exposed _) t (fun z y => f (Fin.snoc z y)) (fun z y => hf _)
  convert hh using 1
  congr 1
  rw [← mean_sub]
  apply mean_congr
  intro ω
  rw [← Fin.comp_snoc, Fin.snoc_init_self]
  unfold completeTest
  rw [freeCount_perm]
  simp only [freeOf_perm]

theorem uniform_prefix_step {α : Type uα} [Fintype α] [DecidableEq α]
    (k : ℕ) (e : Fin (k + 1) → α) (he : Function.Injective e)
    (f : (Fin (k + 1) → α) → ℝ) :
    mean (fun g : Equiv.Perm α => f (g ∘ e)) =
      mean (fun g : Equiv.Perm α => completeTest f (g ∘ Fin.init e)) := by
  have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
    apply (freeOf_true _ _).mpr
    intro i hi
    exact Fin.castSucc_ne_last i (he hi)
  have h := uniform_tagged_completion (Fin.init e) (e (Fin.last k)) ht
    (fun z y => f (Fin.snoc z y))
  simpa only [← Fin.comp_snoc, Fin.snoc_init_self, completeTest, freeCount_perm] using h

theorem prefix_test_bound (d m : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * m)
    (k : ℕ) (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e)
    (f : (Fin k → Position (d + 2)) → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 2) (200 * (d + 2)) => f ((run (d + 2) (200 * (d + 2)) ω) ∘ e)) -
      mean (fun g : State (d + 2) => f (g ∘ e))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
  induction k with
  | zero =>
    have hz (g : State (d + 2)) : g ∘ e = e := by funext i; exact Fin.elim0 i
    simp only [hz, mean_const, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    have he0 : Function.Injective (Fin.init e) := by
      intro i j hij
      exact Fin.castSucc_inj.mp (he hij)
    have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
      apply (freeOf_true _ _).mpr
      intro i hi
      exact Fin.castSucc_ne_last i (he hi)
    have hcount : m ≤ freeCount (freeOf (Fin.init e)) := by
      rw [freeCount_freeOf _ he0]
      omega
    have henergy := centeredPoint_energy_200 d (freeOf (Fin.init e)) (e (Fin.last k)) ht (by omega)
    have hpower : (9 / 10 : ℝ) ^ freeCount (freeOf (Fin.init e)) ≤ (9 / 10 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
    have hz := prefix_one_step_bound (d + 1) (200 * (d + 2)) k e he f hf
    have hestimate :
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          expectedEnergy (d + 1) (initialState (d + 2) (freeOf (Fin.init e)) (e (Fin.last k)) ht)
            (200 * (d + 2))) ≤
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact henergy.trans (by linarith)
    have hnext := ih (by omega) (Fin.init e) he0 (completeTest f) (completeTest_bound f hf)
    rw [uniform_prefix_step k e he f]
    have htri := abs_sub_le
      (mean (fun ω : History (d + 2) (200 * (d + 2)) => f ((run (d + 2) (200 * (d + 2)) ω) ∘ e)))
      (mean (fun ω : History (d + 2) (200 * (d + 2)) => completeTest f ((run (d + 2) (200 * (d + 2)) ω) ∘ Fin.init e)))
      (mean (fun g : State (d + 2) => completeTest f (g ∘ Fin.init e)))
    have hz' := hz.trans hestimate
    push_cast
    nlinarith

end Conditional

end Thorp

end

end OAI
