import OAI.Analysis.LpDimension.Pareto

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u

namespace SubpolynomialLp

lemma geometric_tail_bound (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m N : ℕ) :
    (∑ k ∈ Ico m N, q^k) ≤ q^m/(1-q) := by
  rw [sum_Ico_eq_sum_range]
  simp only [pow_add, ← mul_sum]
  have h := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum
    (range (N-m)) (fun k _ => pow_nonneg hq0 k)
  rw [tsum_geometric_of_lt_one hq0 hq1] at h
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h (pow_nonneg hq0 m)

lemma two_sum_bound (N : ℕ) : (∑ k ∈ range N, (2:ℝ)^k) ≤ 2^N := by
  have h := geom_sum_mul (2:ℝ) N
  norm_num at h
  linarith

lemma dyadic_cauchy (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (N m : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Ico m N, a k)^2 ≤
      (∑ k ∈ range N, (q^k)⁻¹*(a k)^2) * (q^m/(1-q)) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (Ico m N)
    (f := fun k => (q^k)⁻¹*(a k)^2) (g := fun k => q^k) (r := a)
    (fun k _ => by positivity) (fun k _ => by positivity)
    (fun k _ => by rw [mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul])
  have he : (∑ k ∈ Ico m N, (q^k)⁻¹*(a k)^2) ≤
      ∑ k ∈ range N, (q^k)⁻¹*(a k)^2 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_range.mpr (mem_Ico.mp hk).2
    · intro k _ _
      positivity
  exact h.trans (mul_le_mul he (geometric_tail_bound q hq0.le hq1 m N)
    (sum_nonneg (fun k _ => pow_nonneg hq0.le k)) (sum_nonneg (fun k _ => by positivity)))

lemma dyadic_interpolation (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (A : ℝ) (a : ℕ → ℝ), 0 < A →
      (∀ k, 0 ≤ a k) → (∀ k < N, a k ≤ A*2^k) →
      (∑ k ∈ range N, a k)^p ≤ C*A^(p-2)*
        ∑ k ∈ range N, (((2:ℝ)^(2-p))^k)⁻¹ * (a k)^2 := by
  let q : ℝ := (2:ℝ)^(2-p)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let C : ℝ := 4*8^(p-2)/(1-q)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N A a hA ha haB
  let S : ℝ := ∑ k ∈ range N, a k
  let E : ℝ := ∑ k ∈ range N, (q^k)⁻¹*(a k)^2
  change S^p ≤ C*A^(p-2)*E
  have hS : 0 ≤ S := sum_nonneg (fun k _ => ha k)
  have hE : 0 ≤ E := sum_nonneg (fun k _ => by positivity)
  have hSp : S^p = S^2*S^(p-2) := by
    rw [← Real.rpow_two, ← Real.rpow_add' hS (by linarith : 2+(p-2) ≠ 0)]
    congr 1
    ring
  have hglobal : S^2 ≤ E/(1-q) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero, div_eq_mul_inv, one_mul] using
      dyadic_cauchy q hq0 hq1 N 0 a
  have hbound : S ≤ A*2^N := by
    calc
      S ≤ ∑ k ∈ range N, A*2^k := sum_le_sum (fun k hk => haB k (mem_range.mp hk))
      _ = A*∑ k ∈ range N, (2:ℝ)^k := (mul_sum _ _ _).symm
      _ ≤ A*2^N := mul_le_mul_of_nonneg_left (two_sum_bound N) hA.le
  have hnorm : (8*A)^(p-2) = 8^(p-2)*A^(p-2) := Real.mul_rpow (by norm_num) hA.le
  by_cases hs : S ≤ 4*A
  · have hsmall : S^(p-2) ≤ (8*A)^(p-2) := Real.rpow_le_rpow hS (by linarith) (by linarith)
    calc
      S^p = S^2*S^(p-2) := hSp
      _ ≤ (E/(1-q)) * ((8*A)^(p-2)) := mul_le_mul hglobal hsmall (by positivity) (by positivity)
      _ ≤ C*A^(p-2)*E := by
        have hn : 0 ≤ (E/(1-q))*((8*A)^(p-2)) := by positivity
        calc
          _ ≤ 4*((E/(1-q))*((8*A)^(p-2))) := by linarith
          _ = _ := by rw [hnorm]; dsimp [C]; ring
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity : 0 < 4*A) (le_of_not_ge hs)
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ S/(4*A) by apply (le_div_iff₀ (by positivity)).mpr; linarith)
    (by norm_num : (1:ℝ) < 2)
  have hmS : A*2^m ≤ S/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*A)).mp hmlo
    nlinarith
  have hmN : m ≤ N := by
    by_contra h
    have hNm : N ≤ m := by omega
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hNm
    have hmul := mul_le_mul_of_nonneg_left hpow hA.le
    linarith
  have hlow : (∑ k ∈ range m, a k) ≤ S/4 := by
    calc
      _ ≤ ∑ k ∈ range m, A*2^k := sum_le_sum (fun k hk => haB k (lt_of_lt_of_le (mem_range.mp hk) hmN))
      _ = A*∑ k ∈ range m, (2:ℝ)^k := (mul_sum _ _ _).symm
      _ ≤ A*2^m := mul_le_mul_of_nonneg_left (two_sum_bound m) hA.le
      _ ≤ S/4 := hmS
  have hsplit : S = (∑ k ∈ range m, a k)+(∑ k ∈ Ico m N, a k) :=
    (sum_range_add_sum_Ico a hmN).symm
  have htail0 : 0 ≤ ∑ k ∈ Ico m N, a k := sum_nonneg (fun k _ => ha k)
  have hhalf : S ≤ 2*∑ k ∈ Ico m N, a k := by linarith
  have htail := dyadic_cauchy q hq0 hq1 N m a
  have hsq : S^2 ≤ 4*E*(q^m/(1-q)) := by
    have hh := sq_le_sq₀ hS (by positivity) |>.mpr hhalf
    nlinarith
  have hbase : S/(8*A) ≤ 2^m := by
    have h := (div_lt_iff₀ (by positivity : 0 < 4*A)).mp hmhi
    rw [pow_succ] at h
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hpow : S^(p-2) ≤ (8*A)^(p-2)*(2^m)^(p-2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow hS _ (by linarith)
    have h := (div_le_iff₀ (by positivity : 0 < 8*A)).mp hbase
    nlinarith
  have hcancel : q^m * (2^m : ℝ)^(p-2) = 1 := by
    dsimp [q]
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    rw [show (2-p)*(m:ℝ)+(m:ℝ)*(p-2) = 0 by ring, Real.rpow_zero]
  calc
    S^p = S^2*S^(p-2) := hSp
    _ ≤ (4*E*(q^m/(1-q)))*((8*A)^(p-2)*(2^m)^(p-2)) :=
      mul_le_mul hsq hpow (by positivity) (by positivity)
    _ = C*A^(p-2)*E := by
      rw [hnorm]
      calc
        _ = (4*8^(p-2)/(1-q))*A^(p-2)*E*(q^m*(2^m : ℝ)^(p-2)) := by ring
        _ = _ := by rw [hcancel, mul_one]

end SubpolynomialLp

end

end OAI
