import OAI.Probability.RandomSAT.Variance

namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def capMultiplier (k : ℕ) : ℕ := 2^(k + 1)

def mainCap (n k : ℕ) : ℕ := capMultiplier k * n

def center (n k : ℕ) : ℝ :=
  lifetimeMean k (mainCap n k) (Finset.univ : Finset (Assignment n)) / n

def varianceConstant (k : ℕ) : ℝ :=
  2 * (capMultiplier k : ℝ)^3 * k * (2 * k + capMultiplier k + 2)

theorem capMultiplier_pos (k : ℕ) : 0 < capMultiplier k := by
  unfold capMultiplier
  positivity

theorem replacementBlock_le {n k : ℕ} (hn : 1 ≤ n) :
    (replacementBlock n k : ℝ) ≤ (2 * k + 1) * replacementScale n k := by
  have ha := replacementScale_one_le (k := k) hn
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (k : ℝ) * replacementScale n k by positivity)
  change (replacementBlock n k : ℝ) < 2 * k * replacementScale n k + 1 at hc
  nlinarith

theorem replacementError_mul {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * replacementError n k = replacementScale n k := by
  have ha := replacementScale_pos (k := k) hn
  have hp : replacementScale n k ^ (k - 1) * replacementScale n k = (n : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hk, replacementScale_pow hn hk]
  unfold replacementError
  rw [inv_pow]
  rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ (ne_of_gt ha))]
  nlinarith [hp]

theorem integrated_forcing_capped {n k L : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    ∑ j ∈ Finset.range (L * n), forcedFractionMean n k j ≤
      ((L : ℝ) * k * (2 * k + L + 2)) * replacementScale n k := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have h := integrated_forcing_finite hk hn (L * n)
  have hpartial : (∑ j ∈ Finset.range (L * n), forcedFractionMean n k j) ≤
      ∑ j ∈ Finset.range (L * n + 1), forcedFractionMean n k j := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (uniformMean_nonneg (fun _ => by positivity))
  have heps := replacementError_mul (k := k) hn0 (by omega)
  have hg := replacementBlock_le (k := k) (by omega : 1 ≤ n)
  have ha := replacementScale_pos (k := k) hn0
  have he0 := replacementError_nonneg n k
  have hclean : (replacementBlock n k : ℝ) * ((L * n : ℕ) : ℝ) * ((k : ℝ) / n) +
      ((L * n + 1 : ℕ) : ℝ) * ((L * n : ℕ) : ℝ) * ((k : ℝ) / n) * replacementError n k =
      (L : ℝ) * k * replacementBlock n k +
        ((L : ℝ) * n + 1) * L * k * replacementError n k := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp
  rw [hclean] at h
  have he : replacementError n k ≤ replacementScale n k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) he0]
  have hg' := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ L * k)
  have he' := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ L * k)
  have hp : ((L : ℝ) * n + 1) * L * k * replacementError n k =
      (L : ℝ)^2 * k * replacementScale n k + L * k * replacementError n k := by
    nlinarith [congrArg (fun x : ℝ => (L : ℝ)^2 * k * x) heps]
  rw [hp] at h
  nlinarith

theorem variance_capped {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    lifetimeVariance k (mainCap n k) (Finset.univ : Finset (Assignment n)) ≤
      varianceConstant k * n * replacementScale n k ^ 2 := by
  have hL : (1 : ℝ) ≤ capMultiplier k := by exact_mod_cast capMultiplier_pos k
  have hv := lifetimeVariance_forcing_bound (n := n) (k := k) (M := mainCap n k)
    (L := capMultiplier k) (by omega) (by omega) hL (by simp [mainCap])
  have hf := integrated_forcing_capped (L := capMultiplier k) hk hn
  have hmul := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ 2 * (mainCap n k : ℝ) * capMultiplier k * replacementScale n k by
      have ha := replacementScale_pos (k := k) (by omega : 0 < n)
      positivity)
  apply hv.trans
  exact hmul.trans_eq (by simp only [mainCap, Nat.cast_mul, varianceConstant]; ring)

theorem uniform_chebyshev {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {t : ℝ} (ht : 0 < t) :
    uniformProbability (fun a => t ≤ |f a - uniformMean f|) ≤ uniformVariance f / t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht), uniformProbability_eq_mean, ← uniformMean_mul_const]
  apply uniformMean_mono
  intro a
  by_cases h : t ≤ |f a - uniformMean f|
  · simp only [ite_eq_left h, one_mul]
    nlinarith [sq_abs (f a - uniformMean f)]
  · simp only [ite_eq_right h, zero_mul]
    exact sq_nonneg _

theorem alive_univ (n : ℕ) : alive (Finset.univ : Finset (Assignment n)) = 1 := by
  simp [alive]

theorem uniformProbability_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (p : (Fin (m + 1) → α) → Prop) :
    uniformProbability p = uniformMean (fun C : α => uniformProbability
      (fun F : Fin m → α => p (Fin.cons C F))) := by
  rw [uniformProbability_eq_mean, uniformMean_fin_succ]
  apply uniformMean_congr
  intro C
  exact (uniformProbability_eq_mean _).symm

theorem lifetime_tail_probability {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M)
    (S : Finset (Assignment n)) :
    uniformProbability (fun F : Formula n k M => S.Nonempty ∧ (m : ℝ) ≤ lifetime k M S F) =
      survival k m S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  induction m generalizing M S with
  | zero =>
    rw [uniformProbability_eq_mean, survival_zero]
    have he : (fun F : Formula n k M => if S.Nonempty ∧ (0 : ℝ) ≤ lifetime k M S F
        then (1 : ℝ) else 0) = fun _ => alive S := by
      funext F
      simp only [and_iff_left (lifetime_nonneg S F), alive]
    simp only [Nat.cast_zero, he, uniformMean_const]
  | succ m ih =>
    cases M with
    | zero => omega
    | succ M =>
      rw [uniformProbability_fin_succ]
      have he (C : ProperClause n k) (F : Formula n k M) :
          (S.Nonempty ∧ ((m + 1 : ℕ) : ℝ) ≤ lifetime k (M + 1) S (Fin.cons C F)) ↔
          (addClause S C).Nonempty ∧ (m : ℝ) ≤ lifetime k M (addClause S C) F := by
        rw [lifetime_cons, Nat.cast_add, Nat.cast_one]
        by_cases hC : (addClause S C).Nonempty
        · have hS : S.Nonempty := hC.mono (addClause_subset S C)
          simp only [hS, hC, alive, ite_true, true_and]
          constructor <;> intro h <;> linarith
        · have hempty : addClause S C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
          simp only [hempty, alive_empty, lifetime_empty, add_zero, Finset.not_nonempty_empty,
            false_and]
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
          constructor
          · rintro ⟨_, hh⟩; linarith
          · exact False.elim
      rw [survival_succ]
      apply uniformMean_congr
      intro C
      exact (uniformProbability_congr (he C)).trans (ih (M := M) (by omega) (addClause S C))

theorem properSATProbability_eq_lifetime_tail {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    properSATProbability n k m = uniformProbability (fun F : Formula n k M =>
      (m : ℝ) ≤ lifetime k M Finset.univ F) := by
  rw [properSATProbability_eq_survival, ← lifetime_tail_probability hkn hm]
  congr 1
  funext F
  simp

def delta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (4 * k)

def eta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (2 * k)

def fluctuationWindow (n k : ℕ) : ℝ := (n : ℝ) ^ (1 - delta k)

def concentrationError (n k : ℕ) : ℝ := varianceConstant k * (n : ℝ) ^ (-eta k)

theorem delta_pos {k : ℕ} (hk : 3 ≤ k) : 0 < delta k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold delta
  exact div_pos (by linarith) (by positivity)

theorem delta_lt_half {k : ℕ} (hk : 3 ≤ k) : delta k < 1 / 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [delta, div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * k)]
  linarith

theorem eta_eq_twice_delta (k : ℕ) : eta k = 2 * delta k := by
  unfold eta delta
  ring

theorem varianceConstant_nonneg (k : ℕ) : 0 ≤ varianceConstant k := by
  unfold varianceConstant
  positivity

theorem fluctuationWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < fluctuationWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem concentrationError_nonneg (n k : ℕ) : 0 ≤ concentrationError n k :=
  mul_nonneg (varianceConstant_nonneg k) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem variance_window_identity {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * replacementScale n k ^ 2 =
      fluctuationWindow n k ^ 2 * (n : ℝ)^(-eta k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hexp : 1 + (1 / (k : ℝ)) * 2 = (1 - delta k) * 2 + -eta k := by
    unfold delta eta
    field_simp
    ring
  calc
    _ = (n : ℝ)^(1 + (1 / (k : ℝ)) * 2) := by
      rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_mul hn'.le, Real.rpow_two]
      rfl
    _ = (n : ℝ)^((1 - delta k) * 2 + -eta k) := by rw [hexp]
    _ = _ := by
      rw [Real.rpow_add hn', Real.rpow_mul hn'.le, Real.rpow_two]
      rfl

theorem concentration_capped {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    uniformProbability (fun F : Formula n k (mainCap n k) =>
      fluctuationWindow n k ≤ |lifetime k (mainCap n k) Finset.univ F -
        (n : ℝ) * center n k|) ≤ concentrationError n k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause (by omega)
  have hn0 : 0 < n := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
  have hm : (n : ℝ) * center n k = lifetimeMean k (mainCap n k) (Finset.univ : Finset (Assignment n)) := by
    unfold center
    field_simp
  rw [hm]
  have h := uniform_chebyshev (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fluctuationWindow_pos (k := k) hn0)
  apply h.trans
  have hv := div_le_div_of_nonneg_right (variance_capped hk hn)
    (sq_nonneg (fluctuationWindow n k))
  apply hv.trans_eq
  have hid := variance_window_identity (k := k) hn0 (by omega)
  unfold concentrationError
  calc
    _ = varianceConstant k * ((n : ℝ) * replacementScale n k^2) / fluctuationWindow n k^2 := by ring
    _ = _ := by
      rw [hid]
      field_simp [ne_of_gt (fluctuationWindow_pos (k := k) hn0)]

theorem center_nonneg (n k : ℕ) : 0 ≤ center n k := by
  unfold center lifetimeMean
  exact div_nonneg (uniformMean_nonneg (fun F => lifetime_nonneg _ F)) (Nat.cast_nonneg _)

theorem center_le_capMultiplier {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ capMultiplier k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_mono (fun F : Formula n k (mainCap n k) => lifetime_le Finset.univ F)
  rw [uniformMean_const] at h
  unfold center lifetimeMean
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  simpa [mainCap] using h

theorem properSATProbability_center_upper {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    properSATProbability n k m ≤ concentrationError n k := by
  rw [properSATProbability_eq_lifetime_tail (by omega) hm]
  apply (uniformProbability_mono (fun F hF => ?_)).trans (concentration_capped hk hn)
  exact le_trans (by linarith) (le_abs_self _)

theorem properSATProbability_center_lower {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    1 - concentrationError n k ≤ properSATProbability n k m := by
  let : Nonempty (ProperClause n k) := nonempty_properClause (by omega)
  rw [properSATProbability_eq_lifetime_tail (by omega) hm]
  have h := uniformProbability_mono (p := fun F : Formula n k (mainCap n k) =>
    ¬ (m : ℝ) ≤ lifetime k (mainCap n k) Finset.univ F)
    (q := fun F => fluctuationWindow n k ≤
      |lifetime k (mainCap n k) Finset.univ F - (n : ℝ) * center n k|) (fun F hF => by
        have hh : lifetime k (mainCap n k) Finset.univ F < m := lt_of_not_ge hF
        exact le_trans (by linarith) (neg_le_abs _))
  rw [uniformProbability_not] at h
  linarith [concentration_capped hk hn]

end


end FixedClauseThreshold

end OAI
