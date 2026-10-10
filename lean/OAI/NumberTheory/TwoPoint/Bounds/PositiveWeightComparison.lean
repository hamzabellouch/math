import OAI.NumberTheory.TwoPoint.Walks.WeightedWordComparison
import OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail

namespace OAI

/-! Finite-interval comparison for the positive tuple majorant used in
deletion costs. The selected-prime values are kept in one bounded
coefficient table; no subset expansion is needed. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def positivePrimeTable {t : ℕ} (p : Fin t → ℕ) (r : ℕ)
    (bits : BooleanCube t) : ℝ :=
  (4 : ℝ) ^ r * ∏ i, ((if bits i then 1 else 0) + 1 / (p i : ℝ))

lemma positivePrimeTable_nonneg {t : ℕ} (p : Fin t → ℕ) (r : ℕ)
    (bits : BooleanCube t) : 0 ≤ positivePrimeTable p r bits := by
  apply mul_nonneg (pow_nonneg (by norm_num) _)
  apply prod_nonneg
  intro i _
  split_ifs <;> positivity

lemma positivePrimeTable_bound {t : ℕ} (p : Fin t → ℕ)
    (hp : ∀ i, 1 ≤ p i) (r : ℕ) (bits : BooleanCube t) :
    positivePrimeTable p r bits ≤ (4 : ℝ) ^ r * (2 : ℝ) ^ t := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  calc
    _ ≤ ∏ _i : Fin t, (2 : ℝ) := by
      apply prod_le_prod₀
      · intro i _
        split_ifs <;> positivity
      · intro i _
        have hpi : (1 : ℝ) ≤ p i := by exact_mod_cast hp i
        have hi : 1 / (p i : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hpi
        split_ifs <;> linarith
    _ = _ := by simp

lemma positivePrimeTable_budget {t : ℕ} (p : Fin t → ℕ)
    (hp : ∀ i, 1 ≤ p i) (r : ℕ) (L : ℝ)
    (hL : 4800 ≤ L) (ht : (t : ℝ) ≤ L ^ 2)
    (hr : (r : ℝ) ≤ 100 * Real.log L) (bits : BooleanCube t) :
    |positivePrimeTable p r bits| ≤ Real.exp (L ^ 4) := by
  rw [abs_of_nonneg (positivePrimeTable_nonneg p r bits)]
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ (4 : ℝ) ^ r * (2 : ℝ) ^ t := positivePrimeTable_bound p hp r bits
    _ ≤ (Real.exp 4) ^ r * (Real.exp 2) ^ t :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h4 r)
        (pow_le_pow_left₀ (by norm_num) h2 t) (by positivity) (by positivity)
    _ = Real.exp ((r : ℝ) * 4 + (t : ℝ) * 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hquad := mul_nonneg hL0 (show 0 ≤ L - 400 by linarith)
      have hfour := mul_nonneg (sq_nonneg L) (show 0 ≤ L ^ 2 - 3 by nlinarith)
      nlinarith

lemma positivePrimeTable_actual {t : ℕ} (S : Finset ℕ) (e : Fin t ≃ S)
    (r : ℕ) (n : ℤ) :
    positivePrimeTable (fun i => (e i).val) r (fun i => decide (((e i).val : ℤ) ∣ n)) =
      (4 : ℝ) ^ r * positivePrimeWeight S n := by
  unfold positivePrimeTable positivePrimeWeight
  simp only [decide_eq_true_eq]
  congr 1
  rw [← prod_coe_sort S (fun p : ℕ => (if (p : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ))]
  exact e.prod_comp (fun p : S =>
    (if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p.val : ℝ))

theorem BravermanDepth22Input.eventually_positive_weight_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (t r Ninput : ℕ) (p : Fin t → ℕ),
      (∀ i, 1 ≤ p i) → (t : ℝ) ≤ L ^ 2 → (r : ℝ) ≤ 100 * Real.log L →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (pindex : Fin t → Fin Ninput)
        (c : AC0Circuit Ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        positivePrimeTable p r (fun i => bits (pindex i)) * c.indicator bits
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_weighted_word_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro m s _ hm hmexp hcop hs t r Ninput p hp ht hr coord test pindex c hc hsize a N hN
  let qindex : Fin 0 → Fin 0 → Fin Ninput := fun i => Fin.elim0 i
  let f : (Fin 0 → Finset (Fin 0)) → BooleanCube t → ℝ :=
    fun _ bits => positivePrimeTable p r bits
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hh := hb m s hm hmexp hcop hs 0 0 t Ninput 0
    (by simpa only [Nat.cast_zero] using (Real.exp_pos L).le)
    (by simpa only [Nat.cast_zero] using hlog)
    (by simp only [Nat.cast_zero]; linarith) ht coord test qindex pindex f c
    (fun b => positivePrimeTable_budget p hp r L hL ht hr b.2) hc hsize a N hN
  have he (z : ∀ j, ZMod (s j)) :
      (if (∀ i : Fin 0, (activeState (fun j => residueCircuitInputs s coord test z
          (qindex i j))).card ≤ 0) ∧ c.eval (residueCircuitInputs s coord test z) = true
        then f (fun i => activeState (fun j => residueCircuitInputs s coord test z (qindex i j)))
          (fun i => residueCircuitInputs s coord test z (pindex i)) else 0) =
      positivePrimeTable p r (fun i => residueCircuitInputs s coord test z (pindex i)) *
        c.indicator (residueCircuitInputs s coord test z) := by
    simp only [Fin.forall_fin_zero, true_and, f, AC0Circuit.indicator]
    split_ifs <;> simp
  dsimp only at hh ⊢
  simpa only [he] using hh

end TwoPointCorrelations

end OAI
