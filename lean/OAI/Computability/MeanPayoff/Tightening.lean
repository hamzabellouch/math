import OAI.Computability.MeanPayoff.Orientation

namespace OAI

section

namespace MeanPayoff

theorem globalJ_quadratic (n Bmax : ℕ) : 2 * globalS Bmax ^ 2 ≤ globalJ n Bmax := by
  have hs : 1 ≤ globalS Bmax := le_trans (by norm_num) (globalS_large Bmax)
  have hx : globalS Bmax ≤ globalS Bmax * (n + 1) := by nlinarith
  have hpow : globalS Bmax ^ 2 ≤ globalS Bmax ^ 6 :=
    pow_le_pow_right₀ hs (by norm_num)
  have hpow' := Nat.pow_le_pow_left hx 6
  unfold globalJ
  omega

theorem geometric_error (k : ℕ) (hk : 16 ≤ k) :
    (k : ℚ) * (1 / 2 : ℚ) ^ k ≤ 1 / 4096 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : 0 ≤ (1 / 2 : ℚ) ^ k := pow_nonneg (by norm_num) _
    have hkk : 1 ≤ (k : ℚ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hm := mul_nonneg (sub_nonneg.mpr hkk) hp
    rw [pow_succ]
    push_cast
    nlinarith only [hm, ih]

theorem orientation_error_small (n Bmax : ℕ) :
    ((globalG Bmax + 1 : ℕ) : ℚ) * orientationError n Bmax ≤ 1 / 16 := by
  have hs := globalS_lower Bmax
  have hslarge := globalS_large Bmax
  have hJ := globalJ_quadratic n Bmax
  have hsg : globalG Bmax + 1 ≤ globalS Bmax := by omega
  have hprod : 2 * (globalG Bmax + 1) * globalS Bmax ≤ globalJ n Bmax := by
    nlinarith only [hJ, hsg]
  have hJlarge : 16 ≤ globalJ n Bmax := by nlinarith only [hJ, hslarge]
  have hspos : (0 : ℚ) < globalS Bmax := by exact_mod_cast (show 0 < globalS Bmax by omega)
  have hs' : (131072 : ℚ) * (globalG Bmax + 1) ≤ globalS Bmax := by exact_mod_cast hs
  have hfirst : ((globalG Bmax + 1 : ℕ) : ℚ) * (256 / (globalS Bmax : ℚ)) ≤ 1 / 512 := by
    rw [← mul_div_assoc, div_le_iff₀ hspos]
    push_cast
    linarith only [hs']
  have hp' : (2 : ℚ) * (globalG Bmax + 1) * globalS Bmax ≤ globalJ n Bmax := by
    exact_mod_cast hprod
  have hsecond := mul_le_mul_of_nonneg_right hp' (epsilon_nonneg n Bmax)
  have hge := geometric_error (globalJ n Bmax) hJlarge
  change (globalJ n Bmax : ℚ) * epsilon n Bmax ≤ 1 / 4096 at hge
  unfold orientationError
  push_cast at hfirst ⊢
  nlinarith only [hfirst, hsecond, hge]

theorem orient_high_small (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orient G P hR lower I).probability (fun O => ¬HighAlternative I P y O) ≤ 1 / 16 := by
  apply le_trans (orient_high_bound G P hR lower hLower I y hy hc)
  apply le_trans _ (orientation_error_small G.n Bmax)
  apply mul_le_mul_of_nonneg_right _ (orientationError_nonneg _ _)
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  unfold globalG
  exact_mod_cast (show Nat.clog 2 I.width ≤ 1 + Nat.clog 2 (Bmax + 1) + 1 by omega)

theorem orient_low_small (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orient G P hR lower I).probability (fun O => ¬LowAlternative I P z O) ≤ 1 / 16 := by
  apply le_trans (orient_low_bound G P hR lower hLower I z hz hc)
  apply le_trans _ (orientation_error_small G.n Bmax)
  apply mul_le_mul_of_nonneg_right _ (orientationError_nonneg _ _)
  have hc := Nat.clog_mono_right 2 (I.bounded.trans (Nat.le_succ Bmax))
  change Nat.clog 2 I.width ≤ Nat.clog 2 (Bmax + 1) at hc
  unfold globalG
  exact_mod_cast (show Nat.clog 2 I.width ≤ 1 + Nat.clog 2 (Bmax + 1) + 1 by omega)


open scoped Classical

theorem RandomTree.filter_le_badCount {α : Type} (P : α → Prop) (p : α → Bool)
    (as : List α) (h : ∀ a ∈ as, p a = true → ¬ P a) :
    (as.filter p).length ≤ badCount P as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    by_cases ha : p a = true
    · have hn := h a (List.mem_cons_self ..) ha
      simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons, badCount, ite_eq_right hn]
      omega
    · have hfalse : p a = false := Bool.eq_false_iff.mpr ha
      simp only [List.filter_cons, hfalse, Bool.false_eq_true, ↓reduceIte, badCount]
      split_ifs <;> omega

theorem bool_filter_partition {α : Type} (as : List α) (p : α → Bool) :
    (as.filter p).length + (as.filter (fun a => !p a)).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    cases h : p a <;> simp only [List.filter_cons, h, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

theorem exception_retained {n : ℕ} {P : Budgets n} (os : List (Orientation P))
    {O : Orientation P} (hO : O ∈ os) {H : SmallSet P} (hH : H ∈ O.exceptions) :
    H ∈ (combineOrientations os).exceptions := by
  exact List.mem_flatten.mpr ⟨O.exceptions, List.mem_map.mpr ⟨O, hO, rfl⟩, hH⟩

theorem combine_high_failure {n : ℕ} {P : Budgets n} (w : Fin n → ℚ)
    (S : Finset (Fin n)) (b : ℚ) (os : List (Orientation P))
    (hf : ¬ Alternative true w S b (combineOrientations os)) :
    os.length ≤ 2 * RandomTree.badCount (Alternative true w S b) os := by
  have hc : 2 * (os.filter (fun o => o.chooseY)).length ≤ os.length := by
    by_contra hn
    apply hf
    exact Or.inl (by simp [combineOrientations, Nat.lt_of_not_ge hn])
  have hb := RandomTree.filter_le_badCount (Alternative true w S b) (fun o => !o.chooseY) os
    (by
      intro O hO hn hgood
      rcases hgood with hside | ⟨H, hH, hm⟩
      · simp [hside] at hn
      · exact hf (Or.inr ⟨H, exception_retained os hO hH, hm⟩))
  have hp := bool_filter_partition os (fun o => o.chooseY)
  omega

theorem combine_low_failure {n : ℕ} {P : Budgets n} (w : Fin n → ℚ)
    (S : Finset (Fin n)) (b : ℚ) (os : List (Orientation P))
    (hf : ¬ Alternative false w S b (combineOrientations os)) :
    os.length ≤ 2 * RandomTree.badCount (Alternative false w S b) os := by
  have hc : os.length < 2 * (os.filter (fun o => o.chooseY)).length := by
    by_contra hn
    apply hf
    exact Or.inl (by simp [combineOrientations, hn])
  have hb := RandomTree.filter_le_badCount (Alternative false w S b) (fun o => o.chooseY) os
    (by
      intro O hO hn hgood
      rcases hgood with hside | ⟨H, hH, hm⟩
      · simp [hside] at hn
      · exact hf (Or.inr ⟨H, exception_retained os hO hH, hm⟩))
  omega

theorem orientPlus_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).probability
      (fun O => ¬HighAlternative I P y O) ≤ epsilon G.n Bmax := by
  rw [orientPlus, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification _ (HighAlternative I P y)
    (orient_high_small G P hR lower hLower I y hy hc) (globalJ G.n Bmax))
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length _ _)
  intro os hlen hf
  rw [← hlen]
  exact combine_high_failure P.alpha (lowerActive I.a y) P.k os hf

theorem orientPlus_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hLower : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    (orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).probability
      (fun O => ¬LowAlternative I P z O) ≤ epsilon G.n Bmax := by
  rw [orientPlus, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification _ (LowAlternative I P z)
    (orient_low_small G P hR lower hLower I z hz hc) (globalJ G.n Bmax))
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length _ _)
  intro os hlen hf
  rw [← hlen]
  exact combine_low_failure P.beta (upperActive I.b z) P.m os hf

end MeanPayoff

namespace MeanPayoff
open scoped Classical

theorem AdmissibleSub.raise_floor {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {P : Budgets n} {a b a' y : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (haa' : a ≤ a') (ha'b : a' ≤ b) :
    AdmissibleSub F a' b (fun i => max (y i) (a' i)) P := by
  have hp := subsolution_raise_floor laws hy.1 haa' ha'b
  refine ⟨hp.1, (mass_mono (fun i => (P.alpha_pos i).le) ?_).trans hy.2⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 (Finset.mem_filter.mp hi).2⟩

theorem AdmissibleSuper.lower_ceiling {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    (laws : OperatorLaws F) {P : Budgets n} {a b b' z : Vec (Fin n)}
    (hz : AdmissibleSuper F a b z P) (hab' : a ≤ b') (hb'b : b' ≤ b) :
    AdmissibleSuper F a b' (fun i => min (z i) (b' i)) P := by
  have hp := supersolution_lower_ceiling laws hz.1 hab' hb'b
  refine ⟨hp.1, (mass_mono (fun i => (P.beta_pos i).le) ?_).trans hz.2⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2 (Finset.mem_filter.mp hi).2⟩

theorem AdmissibleSub.restrict_ceiling {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b b' y : Vec (Fin n)}
    (hy : AdmissibleSub F a b y P) (hyb' : y ≤ b') : AdmissibleSub F a b' y P :=
  ⟨⟨⟨hy.1.1.1, hyb'⟩, hy.1.2⟩, hy.2⟩

theorem AdmissibleSuper.restrict_floor {n : ℕ} {F : Vec (Fin n) → Vec (Fin n)}
    {P : Budgets n} {a b a' z : Vec (Fin n)}
    (hz : AdmissibleSuper F a b z P) (ha'z : a' ≤ z) : AdmissibleSuper F a' b z P :=
  ⟨⟨⟨ha'z, hz.1.1.2⟩, hz.1.2⟩, hz.2⟩

def tightSub (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (y : Vec (Fin G.n)) : Vec (Fin G.n) :=
  fun i => max (y i - deviation G y I.a + I.delta) (I.a i)
def tightSuper (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (z : Vec (Fin G.n)) : Vec (Fin G.n) :=
  fun i => min (z i + deviation G I.b z - I.delta) (I.b i)

theorem SolveBox.delta_bounds {n Bmax : ℕ} (I : SolveBox n Bmax) :
    4 * globalS Bmax * I.delta ≤ I.width ∧ I.delta ≤ I.C := by
  have hd := Nat.div_mul_le_self I.width (4 * globalS Bmax)
  have hs := globalS_large Bmax
  constructor
  · simpa only [mul_comm, SolveBox.delta] using hd
  · change I.width / (4 * globalS Bmax) ≤ I.width - I.width / (4 * globalS Bmax)
    have hh : 2 * (I.width / (4 * globalS Bmax)) ≤ I.width := by nlinarith
    omega

theorem tightSub_solution (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {y : Vec (Fin G.n)} (hy : Subsolution (operator G) I.a I.b y)
    (hd : (I.C : ℤ) < deviation G y I.a) :
    Subsolution (operator G) I.a I.b (tightSub G I y) := by
  have hh : (I.delta : ℤ) ≤ deviation G y I.a :=
    (by exact_mod_cast I.delta_bounds.2 : (I.delta : ℤ) ≤ I.C).trans hd.le
  have hle : tightSub G I y ≤ y := by
    intro i
    change max (y i - deviation G y I.a + I.delta) (I.a i) ≤ y i
    exact max_le (by omega) (hy.1.1 i)
  refine ⟨⟨fun i => le_max_right _ _, hle.trans hy.1.2⟩, ?_⟩
  intro i hi
  have he : tightSub G I y i = y i - deviation G y I.a + I.delta := by
    apply max_eq_left
    change I.a i < max (y i - deviation G y I.a + I.delta) (I.a i) at hi
    omega
  have hiy := hy.2 i (hi.trans_le (hle i))
  have hm := (operator_laws G).mono (show shift y (-deviation G y I.a + I.delta) ≤ tightSub G I y by
    intro j
    change y j + (-deviation G y I.a + I.delta) ≤ max (y j - deviation G y I.a + I.delta) (I.a j)
    omega) i
  rw [(operator_laws G).translation] at hm
  dsimp only [shift] at hm
  rw [he]
  omega

theorem tightSuper_solution (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    {z : Vec (Fin G.n)} (hz : Supersolution (operator G) I.a I.b z)
    (hd : (I.C : ℤ) < deviation G I.b z) :
    Supersolution (operator G) I.a I.b (tightSuper G I z) := by
  have hh : (I.delta : ℤ) ≤ deviation G I.b z :=
    (by exact_mod_cast I.delta_bounds.2 : (I.delta : ℤ) ≤ I.C).trans hd.le
  have hle : z ≤ tightSuper G I z := by
    intro i
    change z i ≤ min (z i + deviation G I.b z - I.delta) (I.b i)
    exact le_min (by omega) (hz.1.2 i)
  refine ⟨⟨hz.1.1.trans hle, fun i => min_le_right _ _⟩, ?_⟩
  intro i hi
  have he : tightSuper G I z i = z i + deviation G I.b z - I.delta := by
    apply min_eq_left
    change min (z i + deviation G I.b z - I.delta) (I.b i) < I.b i at hi
    omega
  have hiz := hz.2 i ((hle i).trans_lt hi)
  have hm := (operator_laws G).mono (show tightSuper G I z ≤ shift z (deviation G I.b z - I.delta) by
    intro j
    change min (z j + deviation G I.b z - I.delta) (I.b j) ≤ z j + (deviation G I.b z - I.delta)
    omega) i
  rw [(operator_laws G).translation] at hm
  dsimp only [shift] at hm
  rw [he]
  omega

theorem tightSub_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (hd : (I.C : ℤ) < deviation G y I.a) :
    lowerActive I.a (tightSub G I y) ⊆ highCore I y := by
  intro i hi
  have hai := (Finset.mem_filter.mp hi).2
  change I.a i < max (y i - deviation G y I.a + I.delta) (I.a i) at hai
  have hb : (I.width : ℤ) = I.C + I.delta := by
    have h := I.delta_smaller
    unfold SolveBox.C
    omega
  have hdel : 4 * (globalS Bmax : ℤ) * I.delta ≤ I.width := by exact_mod_cast I.delta_bounds.1
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hh : (I.width : ℤ) - 2 * I.delta < y i - I.a i := by omega
  have hm := mul_le_mul_of_nonneg_left hh.le hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by nlinarith only [hm, hdel]⟩

theorem tightSuper_core (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (hd : (I.C : ℤ) < deviation G I.b z) :
    upperActive I.b (tightSuper G I z) ⊆ lowCore I z := by
  intro i hi
  have hai := (Finset.mem_filter.mp hi).2
  change min (z i + deviation G I.b z - I.delta) (I.b i) < I.b i at hai
  have hb : (I.width : ℤ) = I.C + I.delta := by
    have h := I.delta_smaller
    unfold SolveBox.C
    omega
  have hdel : 4 * (globalS Bmax : ℤ) * I.delta ≤ I.width := by exact_mod_cast I.delta_bounds.1
  have hs : (0 : ℤ) ≤ globalS Bmax := Int.natCast_nonneg _
  have hh : (I.width : ℤ) - 2 * I.delta < I.b i - z i := by omega
  have hm := mul_le_mul_of_nonneg_left hh.le hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by nlinarith only [hm, hdel]⟩

theorem tightSub_forces_update (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (r : BoxVector I) (hr : tightSub G I y ≤ r.val) :
    ∃ i, (I.delta : ℤ) ≤ r.val i - I.a i := by
  obtain ⟨i, hi⟩ := deviation_attained G y I.a
  have hh := (le_max_left (y i - deviation G y I.a + I.delta) (I.a i)).trans (hr i)
  exact ⟨i, by omega⟩

theorem tightSuper_forces_update (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (r : BoxVector I) (hr : r.val ≤ tightSuper G I z) :
    ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i := by
  obtain ⟨i, hi⟩ := deviation_attained G I.b z
  have hh : r.val i ≤ z i + deviation G I.b z - I.delta :=
    (hr i).trans (min_le_left (z i + deviation G I.b z - I.delta) (I.b i))
  exact ⟨i, by omega⟩

end MeanPayoff
end

end OAI
