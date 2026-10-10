import OAI.Probability.RandomSAT.Interpolation

namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def properFraction (n k : ℕ) : ℝ := (n.descFactorial k : ℝ) / (n : ℝ)^k

theorem card_injective_lists (n k : ℕ) :
    Fintype.card {f : Fin k → Fin n // Function.Injective f} = n.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

theorem properFraction_probability (n k : ℕ) :
    properFraction n k = uniformProbability (fun f : Fin k → Fin n => Function.Injective f) := by
  unfold properFraction uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card, card_injective_lists, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]

theorem properFraction_nonneg (n k : ℕ) : 0 ≤ properFraction n k := by
  unfold properFraction
  positivity

theorem properFraction_le_one (n k : ℕ) : properFraction n k ≤ 1 := by
  rw [properFraction_probability]
  exact uniformProbability_le_one _

theorem repetition_count_mono {b n k : ℕ} (hbn : b ≤ n) :
    (b : ℝ)^k - b.descFactorial k ≤ (n : ℝ)^k - n.descFactorial k := by
  let e : {f : Fin k → Fin b // ¬ Function.Injective f} ↪
      {f : Fin k → Fin n // ¬ Function.Injective f} := {
    toFun := fun f => ⟨fun i => Fin.castLE hbn (f.val i), by
      intro hinj
      apply f.property
      intro i j hij
      apply hinj
      exact congrArg (Fin.castLE hbn) hij⟩
    inj' := by
      intro f g h
      apply Subtype.ext
      funext i
      apply Fin.castLE_injective hbn
      exact congrFun (congrArg Subtype.val h) i }
  have h := Fintype.card_le_of_embedding e
  have hf (v : ℕ) : Fintype.card {f : Fin k → Fin v // ¬ Function.Injective f} =
      v^k - v.descFactorial k := by
    simp only [Fintype.card_subtype_compl, card_injective_lists, Fintype.card_fun, Fintype.card_fin]
  have hd (v : ℕ) : v.descFactorial k ≤ v^k := by
    have h := Fintype.card_subtype_le (fun f : Fin k → Fin v => Function.Injective f)
    simpa only [card_injective_lists, Fintype.card_fun, Fintype.card_fin] using h
  rw [hf, hf] at h
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  simpa only [Nat.cast_sub (hd _), Nat.cast_pow] using h'

theorem properFraction_mul_kill {b n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    properFraction n k * killFraction b n k =
      (b.descFactorial k : ℝ) / ((2 : ℝ)^k * (n : ℝ)^k) := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction killFraction
  rw [Nat.descFactorial_eq_factorial_mul_choose n k, Nat.descFactorial_eq_factorial_mul_choose b k]
  push_cast
  field_simp

theorem auxiliary_kill_le_repetition {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n)
    (hn : 0 < n) :
    ((b : ℝ) / (2 * n))^k ≤ 1 - properFraction n k +
      properFraction n k * killFraction b n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount := repetition_count_mono (k := k) hbn
  have hq := properFraction_le_one n k
  have hden : (0 : ℝ) < (2 : ℝ)^k * (n : ℝ)^k := by positivity
  have hp : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [properFraction_mul_kill hkn hn]
  unfold properFraction at hq ⊢
  rw [div_le_one (by positivity)] at hq
  rw [div_pow, mul_pow]
  have hnonneg : 0 ≤ (n : ℝ)^k - n.descFactorial k := sub_nonneg.mpr hq
  have hm := mul_le_mul_of_nonneg_right hp hnonneg
  have hd : (b : ℝ)^k - b.descFactorial k ≤
      (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hd hden.le
  have he : (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) /
      ((2 : ℝ)^k * (n : ℝ)^k) = 1 - (n.descFactorial k : ℝ) / (n : ℝ)^k := by
    field_simp
  rw [he, sub_div] at hdiv
  linarith

theorem clauseAverage_alive {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    clauseAverage k alive S = alive S * (1 - killFraction (forcedVariables S).card n k) := by
  by_cases hS : S.Nonempty
  · have h := singleUNSAT_eq hkn S
    have he : (uniformProbability (fun C : ProperClause n k => KillsSolutions S C)) =
        killingProbability k S := by
      apply uniformProbability_congr
      exact fun _ => (and_iff_right hS).symm
    rw [he, killingProbability_of_nonempty S hS] at h
    change killFraction _ _ _ = 1 - clauseAverage k alive S at h
    simp only [alive, ite_eq_left hS, one_mul]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [clauseAverage, addClause, alive_empty, uniformMean_zero]

theorem auxiliaryAverage_le_proper {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    auxiliaryAverage k alive ≤ clauseAverage (n := n) k alive := by
  intro S
  rw [auxiliaryAverage_alive hn, clauseAverage_alive hkn]
  apply mul_le_mul_of_nonneg_left _ (alive_nonneg S)
  apply sub_le_sub_left
  have hb : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := killFraction_le_pow hb hkn hn
  simpa only [forcedFraction, div_mul_eq_div_div_swap] using h

theorem scaled_proper_le_auxiliaryAverage {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    (fun S => properFraction n k * clauseAverage k alive S) ≤ auxiliaryAverage (n := n) k alive := by
  intro S
  change properFraction n k * clauseAverage k alive S ≤ auxiliaryAverage k alive S
  rw [auxiliaryAverage_alive hn, clauseAverage_alive hkn]
  have hb : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := auxiliary_kill_le_repetition hb hkn hn
  have hh : properFraction n k * (1 - killFraction (forcedVariables S).card n k) ≤
      1 - (forcedFraction S / 2)^k := by
    unfold forcedFraction
    rw [div_div]
    rw [mul_comm (n : ℝ) 2]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hh (alive_nonneg S)
  nlinarith

theorem auxiliaryProbability_le_proper {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    auxiliaryProbability n k m ≤ properSATProbability n k m := by
  rw [properSATProbability_eq_survival]
  exact iterate_compare_of_commute (clauseAverage k) (auxiliaryAverage k)
    (fun _ _ h => finiteClauseAverage_mono _ h) (fun _ _ h => finiteClauseAverage_mono _ h)
    (finiteClauseAverage_commute _ _) (auxiliaryAverage_le_proper hn hkn) m Finset.univ

theorem proper_scaled_le_auxiliaryProbability {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    (properFraction n k)^m * properSATProbability n k m ≤ auxiliaryProbability n k m := by
  have hstep := scaled_proper_le_auxiliaryAverage hn hkn
  let B : (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
    fun f S => properFraction n k * clauseAverage k f S
  have hB : Monotone B := by
    intro f g h S
    exact mul_le_mul_of_nonneg_left (finiteClauseAverage_mono _ h S) (properFraction_nonneg n k)
  have hcomm : Function.Commute (auxiliaryAverage (n := n) k) B := by
    intro f
    unfold B auxiliaryAverage embeddedAverage
    rw [finiteClauseAverage_const_mul]
    funext S
    congr 1
    exact congrFun (finiteClauseAverage_commute
      (fun C : AuxiliaryClause n k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause id C))
      (fun C : ProperClause n k => fun σ => SatisfiesClause σ C) f) S
  have hit (j : ℕ) (f : Finset (Assignment n) → ℝ) :
      B^[j] f = (fun S => (properFraction n k)^j * (clauseAverage k)^[j] f S) := by
    induction j with
    | zero => funext S; simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold B clauseAverage
      funext S
      rw [uniformMean_const_mul]
      rw [Function.iterate_succ_apply', pow_succ]
      ring
  have h := iterate_compare_of_commute (auxiliaryAverage k) B
    (fun _ _ h => finiteClauseAverage_mono _ h) hB hcomm hstep m Finset.univ
  rw [hit] at h
  rw [properSATProbability_eq_survival]
  exact h

def repeatPairs (k : ℕ) : ℝ := (k.choose 2 : ℝ)

@[simp] theorem repeatPairs_zero : repeatPairs 0 = 0 := by norm_num [repeatPairs]

theorem repeatPairs_succ (k : ℕ) : repeatPairs (k + 1) = repeatPairs k + k := by
  simp only [repeatPairs, Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
  ring

theorem repeatPairs_nonneg (k : ℕ) : 0 ≤ repeatPairs k := Nat.cast_nonneg _

theorem properFraction_succ {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    properFraction n (k + 1) = properFraction n k * (1 - (k : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ]
  field_simp

theorem properFraction_lower {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    1 - repeatPairs k / n ≤ properFraction n k := by
  induction k with
  | zero => simp [properFraction]
  | succ k ih =>
    have hkn' : k ≤ n := by omega
    have hi := ih hkn'
    have hle := properFraction_le_one n k
    have hprod := mul_le_mul_of_nonneg_right hle (show 0 ≤ (k : ℝ) / n by positivity)
    rw [properFraction_succ hn hkn', repeatPairs_succ, add_div]
    nlinarith

theorem auxiliarySurvival_nonneg {n k : ℕ} (m : ℕ) (S : Finset (Assignment n)) :
    0 ≤ auxiliarySurvival k m S := by
  induction m generalizing S with
  | zero => exact alive_nonneg S
  | succ m ih => rw [auxiliarySurvival_succ]; exact uniformMean_nonneg (fun _ => ih _)

theorem auxiliarySurvival_le_one {n k : ℕ} (hn : 0 < n) (m : ℕ) (S : Finset (Assignment n)) :
    auxiliarySurvival k m S ≤ 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  induction m generalizing S with
  | zero => exact alive_le_one S
  | succ m ih =>
    rw [auxiliarySurvival_succ, ← uniformMean_const (α := AuxiliaryClause n k) (1 : ℝ)]
    exact uniformMean_mono (fun _ => ih _)

theorem auxiliaryProbability_nonneg (n k m : ℕ) : 0 ≤ auxiliaryProbability n k m :=
  auxiliarySurvival_nonneg _ _

theorem auxiliaryProbability_le_one {n : ℕ} (hn : 0 < n) (k m : ℕ) :
    auxiliaryProbability n k m ≤ 1 := auxiliarySurvival_le_one hn _ _

theorem finite_model_sandwich {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    (properFraction n k)^m * properSATProbability n k m ≤ auxiliaryProbability n k m ∧
      auxiliaryProbability n k m ≤
        binomialMean (properFraction n k) m (properSATProbability n k) := by
  refine ⟨proper_scaled_le_auxiliaryProbability hn hkn m, ?_⟩
  apply (auxiliaryProbability_le_proper hn hkn m).trans
  rw [← binomialMean_const (properFraction n k) (properSATProbability n k m) m]
  apply binomialMean_mono (properFraction_nonneg n k) (properFraction_le_one n k)
  intro d hd
  exact properSATProbability_antitone hkn hd

theorem thinned_count_mean_bounds {n k m : ℕ} {L : ℝ} (hn : 0 < n) (hkn : k ≤ n)
    (hm : (m : ℝ) ≤ L * n) :
    (m : ℝ) - L * repeatPairs k ≤ binomialMean (properFraction n k) m (fun j => (j : ℝ)) ∧
      binomialMean (properFraction n k) m (fun j => (j : ℝ)) ≤ m := by
  rw [binomialMean_id]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := properFraction_lower hn hkn
  have hu := properFraction_le_one n k
  have h1 := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ repeatPairs k / n by
    exact div_nonneg (repeatPairs_nonneg k) hn'.le)
  have he : L * n * (repeatPairs k / n) = L * repeatPairs k := by field_simp
  rw [he] at h2
  constructor
  · nlinarith
  · nlinarith

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 1 - x by linarith)
  have hh : 1 ≤ Real.exp (2 * x) * (1 - x) := by nlinarith
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp
  rw [← Real.exp_add, show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
  simpa only [mul_comm] using hh

def transferFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ) * repeatPairs k)

def transferLower (k : ℕ) : ℝ := transferFactor k / 2

theorem transferFactor_pos (k : ℕ) : 0 < transferFactor k := Real.exp_pos _

theorem transferLower_pos (k : ℕ) : 0 < transferLower k := div_pos (transferFactor_pos k) (by norm_num)

theorem properFraction_pow_lower {n k m : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (hm : m ≤ mainCap n k) :
    transferFactor k ≤ (properFraction n k)^m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ repeatPairs k / n := div_nonneg (repeatPairs_nonneg k) hn'.le
  have hx : repeatPairs k / n ≤ 1 / 2 := (div_le_iff₀ hn').mpr (by linarith)
  have hbase := (exp_neg_two_le_one_sub hx0 hx).trans (properFraction_lower hn hkn)
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase m
  rw [← Real.exp_nat_mul] at hpow
  apply le_trans _ hpow
  apply Real.exp_le_exp.mpr
  have hm' : (m : ℝ) ≤ (capMultiplier k : ℝ) * n := by exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_right hm' hx0
  have he : ((capMultiplier k : ℝ) * n) * (repeatPairs k / n) =
      (capMultiplier k : ℝ) * repeatPairs k := by field_simp
  rw [he] at hh
  nlinarith

theorem auxiliaryProbability_center_lower {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (herror : concentrationError n k ≤ 1 / 2)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    transferLower k ≤ auxiliaryProbability n k m := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcenter := center_le_capMultiplier (by omega : k ≤ n) hn0
  have hm : m ≤ mainCap n k := by
    have hw := (fluctuationWindow_pos (k := k) hn0).le
    have h := mul_le_mul_of_nonneg_left hcenter hn'.le
    have : (m : ℝ) ≤ (mainCap n k : ℝ) := by
      simp only [mainCap, Nat.cast_mul]
      nlinarith
    exact_mod_cast this
  have hprob := properSATProbability_center_lower hk hn hm hgap
  have hhalf : (1 / 2 : ℝ) ≤ properSATProbability n k m := by linarith
  have hmul := mul_le_mul (properFraction_pow_lower hn0 (by omega) hnrep hm) hhalf
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (properFraction_nonneg n k |> fun h => pow_nonneg h m)
  apply le_trans _ (proper_scaled_le_auxiliaryProbability hn0 (by omega) m)
  simpa only [transferLower, div_eq_mul_inv, one_mul] using hmul

theorem auxiliaryProbability_center_upper {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    auxiliaryProbability n k m ≤ concentrationError n k :=
  (auxiliaryProbability_le_proper (by omega) (by omega) m).trans
    (properSATProbability_center_upper hk hn hm hgap)

theorem binomialMean_square (p : ℝ) (m : ℕ) :
    binomialMean p m (fun j => (j : ℝ)^2) = m * p * (1 - p) + ((m : ℝ) * p)^2 := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [binomialMean]
    have he : binomialMean p m (fun j => ((j + 1 : ℕ) : ℝ)^2) =
        binomialMean p m (fun j => (j : ℝ)^2) + 2 * ((m : ℝ) * p) + 1 := by
      calc
        _ = binomialMean p m (fun j => (j : ℝ)^2 + 2 * j + 1) := by
          apply binomialMean_congr
          intro j _
          push_cast
          ring
        _ = _ := by
          rw [binomialMean_add, binomialMean_add, binomialMean_const_mul,
            binomialMean_id, binomialMean_const]
    rw [he, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem binomialMean_centered_square (p : ℝ) (m : ℕ) :
    binomialMean p m (fun j => ((j : ℝ) - (m : ℝ) * p)^2) = (m : ℝ) * p * (1 - p) := by
  calc
    _ = binomialMean p m (fun j => (j : ℝ)^2 - 2 * ((m : ℝ) * p) * j + ((m : ℝ) * p)^2) := by
      apply binomialMean_congr
      intro j _
      ring
    _ = _ := by
      rw [binomialMean_add, binomialMean_sub, binomialMean_const_mul,
        binomialMean_const, binomialMean_square, binomialMean_id]
      ring

theorem binomialMean_div_const (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun j => f j / c) = binomialMean p m f / c := by
  simp only [div_eq_mul_inv, binomialMean_mul_const]

theorem binomialMean_all_success {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (f : ℕ → ℝ) (hf : ∀ j ≤ m, 0 ≤ f j) :
    p^m * f m ≤ binomialMean p m f := by
  induction m generalizing f with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [binomialMean, pow_succ]
    have h0 := binomialMean_nonneg hp0 hp1 (m := m) (f := f) (fun j hj => hf j (by omega))
    have h1 := ih (fun j => f (j + 1)) (fun j hj => hf (j + 1) (by omega))
    have hm := mul_le_mul_of_nonneg_left h1 hp0
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) h0]

theorem product_lower_two_deviations {κ x y a b : ℝ} (hκ : 0 ≤ κ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : x < 1 → κ ≤ a) (hby : y < 1 → κ ≤ b) :
    κ^2 * (1 - x - y) ≤ a * b := by
  by_cases hx1 : x < 1
  · by_cases hy1 : y < 1
    · have hprod := mul_le_mul (hax hx1) (hby hy1) hκ ha
      have hle : κ^2 * (1 - x - y) ≤ κ^2 :=
        by
          have hh : 1 - x - y ≤ 1 := by linarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg κ)
      nlinarith
    · have hle : κ^2 * (1 - x - y) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
      exact hle.trans (mul_nonneg ha hb)
  · have hle : κ^2 * (1 - x - y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
    exact hle.trans (mul_nonneg ha hb)

def samplingError (n k : ℕ) : ℝ :=
  (capMultiplier k : ℝ) * n / (fluctuationWindow n k)^2

theorem samplingError_nonneg (n k : ℕ) : 0 ≤ samplingError n k := by
  unfold samplingError
  positivity

end


end FixedClauseThreshold

end OAI
