import OAI.NumberTheory.ShortEgyptian.GreedyExistence

namespace OAI

namespace ShortEgyptian

theorem unitSum_le_length_div {d : ℕ} {ns : List ℕ}
    (hd : 0 < d) (hmin : ∀ n ∈ ns, d ≤ n) :
    unitSum ns ≤ (ns.length : ℚ) / d := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hh := (ns.map (fun n : ℕ => (1 : ℚ) / n)).sum_le_length_nsmul ((1 : ℚ) / d)
    (by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact one_div_le_one_div_of_le hdQ (by exact_mod_cast hmin n hn))
  simpa [unitSum, div_eq_mul_inv] using hh

theorem denominator_bound_aux (ns : List ℕ) (hsort : ns.Pairwise (· ≤ ·))
    (hpos : ∀ n ∈ ns, 0 < n) (A P s : ℕ) (hA : 0 < A) (hP : 0 < P)
    (hlen : ns.length ≤ s) (heq : unitSum ns = (A : ℚ) / P) :
    ∀ n ∈ ns, n ≤ (s * P) ^ (2 ^ (ns.length - 1)) := by
  induction ns generalizing A P with
  | nil => simp
  | cons d ns ih =>
    have hd : 0 < d := hpos d (by simp)
    have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
    have hPQ : (0 : ℚ) < P := by exact_mod_cast hP
    have hAQ : (1 : ℚ) ≤ A := by exact_mod_cast hA
    have hsorted := List.pairwise_cons.mp hsort
    have hmin : ∀ n ∈ d :: ns, d ≤ n := by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact le_rfl
      · exact hsorted.1 n hn
    have hbd : (A : ℚ) / P ≤ (s : ℚ) / d := by
      rw [← heq]
      exact (unitSum_le_length_div hd hmin).trans
        (div_le_div_of_nonneg_right (by exact_mod_cast hlen) (le_of_lt hdQ))
    have hdpQ : (d : ℚ) ≤ s * P := by
      have hh := (div_le_div_iff₀ hPQ hdQ).mp hbd
      nlinarith
    have hdp : d ≤ s * P := by exact_mod_cast hdpQ
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hdp.trans (Nat.le_self_pow (by positivity) _)
    have hnslen : 0 < ns.length := List.length_pos_of_mem hn
    have hnpos : 0 < n := hpos n (by simp [hn])
    have hsumpos : 0 < unitSum ns :=
      (by positivity : (0 : ℚ) < 1 / (n : ℚ)).trans_le (unit_le_sum hn)
    have hAeq : (A : ℚ) / P = 1 / (d : ℚ) + unitSum ns := by
      simpa [unitSum_cons] using heq.symm
    have hPAQ : (P : ℚ) < A * d := by
      have hfrac : (1 : ℚ) / d < A / P := by linarith
      have hh := (div_lt_div_iff₀ hdQ hPQ).mp hfrac
      simpa using hh
    have hPA : P < A * d := by exact_mod_cast hPAQ
    have hr : 0 < A * d - P := Nat.sub_pos_of_lt hPA
    have hrem : unitSum ns = ((A * d - P : ℕ) : ℚ) / (P * d : ℕ) := by
      rw [Nat.cast_sub (le_of_lt hPA), Nat.cast_mul, Nat.cast_mul]
      apply (eq_div_iff (ne_of_gt (mul_pos hPQ hdQ))).mpr
      have hh := (div_eq_iff (ne_of_gt hPQ)).mp hAeq
      field_simp at hh ⊢
      nlinarith
    have ihb := ih hsorted.2 (fun x hx => hpos x (by simp [hx]))
      (A * d - P) (P * d) hr (Nat.mul_pos hP hd)
      (by simpa using (show ns.length ≤ s from by simpa using Nat.le_trans (Nat.le_succ ns.length) hlen))
      hrem n hn
    have hbase : s * (P * d) ≤ (s * P) ^ 2 := by nlinarith [hdp]
    calc
      n ≤ (s * (P * d)) ^ (2 ^ (ns.length - 1)) := ihb
      _ ≤ ((s * P) ^ 2) ^ (2 ^ (ns.length - 1)) := Nat.pow_le_pow_left hbase _
      _ = (s * P) ^ (2 ^ ((d :: ns).length - 1)) := by
        rw [← pow_mul]
        congr 1
        simp only [List.length_cons, Nat.add_sub_cancel]
        have hlen' : ns.length = ns.length - 1 + 1 := by omega
        conv_rhs => rw [hlen', pow_succ]
        omega

theorem denominator_bound (ns : List ℕ) (hpos : ∀ n ∈ ns, 0 < n)
    (heq : unitSum ns = 1) {n : ℕ} (hn : n ∈ ns) :
    n ≤ ns.length ^ (2 ^ (ns.length - 1)) := by
  let sorted := ns.mergeSort (fun a b => decide (a ≤ b))
  have hperm : sorted.Perm ns := List.mergeSort_perm ns _
  have hpair : sorted.Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
        (by intros; simp_all; omega) (by intros; simp; omega) ns
  have hsp : ∀ d ∈ sorted, 0 < d := fun d hd => hpos d (hperm.mem_iff.mp hd)
  have hsum : unitSum sorted = (1 : ℚ) / (1 : ℕ) := by
    have hh := (hperm.map (fun n : ℕ => (1 : ℚ) / n)).sum_eq
    simpa [unitSum, heq] using hh.trans heq
  have hh := denominator_bound_aux sorted hpair hsp 1 1 ns.length
    (by omega) (by omega) (by simp [sorted]) hsum n (hperm.mem_iff.mpr hn)
  simpa [sorted] using hh

theorem hard_numerator_bound {b : ℕ} (hb : 2 ≤ b) {ns : List ℕ}
    (he : IsExpansion (b - 1) b ns) :
    b ≤ (ns.length + 1) ^ (2 ^ ns.length) := by
  have hbpos : 0 < b := by omega
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  rw [isExpansion_iff] at he
  have hh : unitSum (b :: ns) = 1 := by
    rw [unitSum_cons, he.2.2, Nat.cast_sub (by omega : 1 ≤ b)]
    push_cast
    field_simp
    ring
  have hh' := denominator_bound (b :: ns)
    (by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hbpos
      · exact lt_of_lt_of_le (by omega : 0 < 2) (he.2.1 n hn)) hh (by simp : b ∈ b :: ns)
  simpa using hh'

theorem expansion_length_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {ns : List ℕ} (he : IsExpansion a b ns) : 0 < ns.length := by
  rw [isExpansion_iff] at he
  by_contra hh
  have hnil : ns = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
  rw [hnil, unitSum_nil] at he
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have := div_pos haQ hbQ
  linarith [he.2.2]

theorem loglog_le_twice_length {b : ℕ} (hb : 2 ≤ b) {ns : List ℕ}
    (he : IsExpansion (b - 1) b ns) :
    Real.log (Real.log (b : ℝ)) ≤ 2 * (ns.length : ℝ) := by
  let k := ns.length
  have hk : 0 < k := expansion_length_pos (by omega : 0 < b - 1) (by omega) he
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k + 1 := by positivity
  have hlogk : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hh : (b : ℝ) ≤ ((k : ℝ) + 1) ^ (2 ^ k) := by
    exact_mod_cast hard_numerator_bound hb he
  have hfirst := Real.log_le_log (lt_trans (by norm_num : (0 : ℝ) < 1) hbR) hh
  rw [Real.log_pow] at hfirst
  have hsecond := Real.log_le_log (Real.log_pos hbR) hfirst
  rw [Real.log_mul (by positivity) (ne_of_gt hlogk)] at hsecond
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hsecond
  have ht : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlt := Real.log_le_self (le_of_lt hlogk)
  have hlk := Real.log_le_sub_one_of_pos hkp
  have hm := mul_le_mul_of_nonneg_left ht (le_of_lt hkR)
  calc
    Real.log (Real.log (b : ℝ)) ≤ (k : ℝ) * Real.log 2 + Real.log (Real.log ((k : ℝ) + 1)) := hsecond
    _ ≤ 2 * (ns.length : ℝ) := by dsimp [k] at *; nlinarith

theorem main_lower (b : ℕ) (hb : 2 ≤ b) :
    (1 / 2 : ℝ) * Real.log (Real.log (b : ℝ)) ≤ (maxMinLength b : ℝ) := by
  obtain ⟨ns, he, hlen⟩ := minLength_attained (show b - 1 < b by omega)
  have hh := loglog_le_twice_length hb he
  have hk := minLength_le_maxMinLength (show 1 ≤ b - 1 by omega) (show b - 1 < b by omega)
  rw [hlen] at hh
  have hkR : (minLength (b - 1) b : ℝ) ≤ maxMinLength b := by exact_mod_cast hk
  linarith

end ShortEgyptian

end OAI
