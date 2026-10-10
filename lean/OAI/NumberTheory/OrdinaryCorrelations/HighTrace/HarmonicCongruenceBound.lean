import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving

theorem harmonic_congruence_bound (s : Finset ℕ) (P B : ℝ) (r a : ℕ)
    (hP : 0 < P) (hB : 0 ≤ B) (hr : P ≤ r)
    (hs : ∀ n ∈ s, P ≤ (n:ℝ) ∧ (n:ℝ) ≤ Real.exp B ∧ n % r = a % r) :
    ∑ n ∈ s, (n:ℝ)⁻¹ ≤ (2+B)/P := by
  have hrpos : 0 < r := by exact_mod_cast hP.trans_le hr
  let lo := s.filter (fun n => n < r)
  let hi := s.filter (fun n => r ≤ n)
  have hunion : s = lo ∪ hi := by
    ext n
    simp only [lo,hi,mem_union,mem_filter]
    constructor
    · intro hn
      rcases lt_or_ge n r with h | h
      · exact Or.inl ⟨hn,h⟩
      · exact Or.inr ⟨hn,h⟩
    · rintro (⟨hn,_⟩ | ⟨hn,_⟩) <;> exact hn
  have hdis : Disjoint lo hi := by
    apply disjoint_left.mpr
    intro n hn hm
    have := (mem_filter.mp hn).2
    have := (mem_filter.mp hm).2
    omega
  have hlo : ∑ n ∈ lo, (n:ℝ)⁻¹ ≤ P⁻¹ := by
    by_cases he : lo.Nonempty
    · obtain ⟨n,hn⟩ := he
      have heq : lo = {n} := by
        apply eq_singleton_iff_unique_mem.mpr
        refine ⟨hn,fun m hm => ?_⟩
        have hm' := hs m (mem_filter.mp hm).1
        have hn' := hs n (mem_filter.mp hn).1
        have hm0 := (mem_filter.mp hm).2
        have hn0 := (mem_filter.mp hn).2
        rw [Nat.mod_eq_of_lt hm0] at hm'
        rw [Nat.mod_eq_of_lt hn0] at hn'
        exact hm'.2.2.trans hn'.2.2.symm
      rw [heq,sum_singleton]
      exact inv_anti₀ hP (hs n (mem_filter.mp hn).1).1
    · simp only [not_nonempty_iff_eq_empty.mp he,sum_empty]
      positivity
  have hinj : Set.InjOn (fun n : ℕ => n/r) hi := by
    intro n hn m hm he
    have hn' := (hs n (mem_filter.mp hn).1).2.2
    have hm' := (hs m (mem_filter.mp hm).1).2.2
    change n/r = m/r at he
    calc
      n = n%r+r*(n/r) := (Nat.mod_add_div n r).symm
      _ = m%r+r*(m/r) := by rw [hn',hm',he]
      _ = m := Nat.mod_add_div m r
  have hsubset : hi.image (fun n => n/r) ⊆ Icc 1 ⌊Real.exp B⌋₊ := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    apply mem_Icc.mpr
    constructor
    · exact Nat.div_pos (mem_filter.mp hn).2 hrpos
    · apply (Nat.div_le_self n r).trans
      exact Nat.le_floor (hs n (mem_filter.mp hn).1).2.1
  have hsum : ∑ n ∈ hi, (n:ℝ)⁻¹ ≤
      (r:ℝ)⁻¹ * (harmonic ⌊Real.exp B⌋₊ : ℝ) := by
    calc
      _ ≤ ∑ n ∈ hi, ((n/r:ℕ):ℝ)⁻¹ * (r:ℝ)⁻¹ := by
        apply sum_le_sum
        intro n hn
        rw [← mul_inv_rev]
        apply inv_anti₀
        · have hquot : 0 < n/r := Nat.div_pos (mem_filter.mp hn).2 hrpos
          positivity
        · exact_mod_cast (show r*(n/r) ≤ n by simpa [mul_comm] using Nat.div_mul_le_self n r)
      _ = (r:ℝ)⁻¹ * ∑ k ∈ hi.image (fun n => n/r), (k:ℝ)⁻¹ := by
        rw [← sum_mul, sum_image hinj]
        ring
      _ ≤ (r:ℝ)⁻¹ * ∑ k ∈ Icc 1 ⌊Real.exp B⌋₊, (k:ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_left
        · exact sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
        · positivity
      _ = _ := by simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  have hhar : (harmonic ⌊Real.exp B⌋₊:ℝ) ≤ 1+B := by
    simpa using harmonic_floor_le_one_add_log (Real.exp B) (Real.one_le_exp hB)
  have hsum' : ∑ n ∈ hi, (n:ℝ)⁻¹ ≤ (1+B)/P := by
    apply hsum.trans
    calc
      _ ≤ (r:ℝ)⁻¹ * (1+B) := mul_le_mul_of_nonneg_left hhar (by positivity)
      _ ≤ P⁻¹*(1+B) := mul_le_mul_of_nonneg_right (inv_anti₀ hP hr) (by linarith)
      _ = _ := by ring
  rw [hunion,sum_union hdis]
  have : P⁻¹+(1+B)/P = (2+B)/P := by ring
  linarith

theorem harmonic_divisor_bound (s : Finset ℕ) (P : ℝ) (D : ℤ)
    (hP : 0 < P) (hD : D ≠ 0)
    (hs : ∀ p ∈ s, Nat.Prime p ∧ P ≤ (p:ℝ) ∧ (p:ℤ) ∣ D) :
    ∑ p ∈ s, (p:ℝ)⁻¹ ≤ Real.log (|(D:ℝ)|+2)/(P*Real.log 2) := by
  have hDn : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  have hsub : s ⊆ D.natAbs.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(hs p hp).1,
      Int.natCast_dvd.mp (hs p hp).2.2,by omega⟩
  have hprod : 2^s.card ≤ D.natAbs := by
    calc
      _ = ∏ _p ∈ s, 2 := by simp
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod (fun p hp => (hs p hp).1.two_le)
      _ ≤ D.natAbs := Nat.le_of_dvd hDn
        ((prod_dvd_prod_of_subset s D.natAbs.primeFactors id hsub).trans
          (Nat.prod_primeFactors_dvd _))
  have hpow : (2:ℝ)^s.card ≤ (D.natAbs:ℝ) := by exact_mod_cast hprod
  have hlog : (s.card:ℝ)*Real.log 2 ≤ Real.log (|(D:ℝ)|+2) := by
    calc
      _ = Real.log ((2:ℝ)^s.card) := (Real.log_pow _ _).symm
      _ ≤ Real.log (D.natAbs:ℝ) := Real.log_le_log (by positivity) hpow
      _ ≤ Real.log (|(D:ℝ)|+2) := by
        apply Real.log_le_log (by exact_mod_cast hDn)
        have he : (D.natAbs:ℝ) = |(D:ℝ)| := by
          simpa only [Int.cast_natCast,Int.cast_abs] using
            congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs D)
        rw [he]
        linarith
  have hsum : ∑ p ∈ s, (p:ℝ)⁻¹ ≤ (s.card:ℝ)/P := by
    simpa [nsmul_eq_mul,div_eq_mul_inv] using
      sum_le_card_nsmul s (fun p : ℕ => (p:ℝ)⁻¹) P⁻¹
        (fun p hp => inv_anti₀ hP (hs p hp).2.1)
  apply hsum.trans
  apply (le_div_iff₀ (mul_pos hP (Real.log_pos (by norm_num)))).mpr
  have he : ((s.card:ℝ)/P)*(P*Real.log 2) = (s.card:ℝ)*Real.log 2 := by
    field_simp
  rwa [he]

theorem harmonic_linear_bound (s : Finset ℕ) (P B : ℝ) (r : ℕ) (a c : ℤ)
    (hP : 0 < P) (hB : 0 ≤ B) (hr : P ≤ (r:ℝ)) (hrp : Nat.Prime r)
    (ha : ¬(r:ℤ) ∣ a)
    (hs : ∀ n ∈ s, P ≤ (n:ℝ) ∧ (n:ℝ) ≤ Real.exp B ∧ (r:ℤ) ∣ a*n+c) :
    ∑ n ∈ s, (n:ℝ)⁻¹ ≤ (2+B)/P := by
  by_cases he : s.Nonempty
  · obtain ⟨n₀,hn₀⟩ := he
    apply harmonic_congruence_bound s P B r n₀ hP hB hr
    intro n hn
    refine ⟨(hs n hn).1,(hs n hn).2.1,?_⟩
    apply Nat.modEq_iff_dvd.mpr
    apply ((Nat.prime_iff_prime_int.mp hrp).dvd_mul).mp _ |>.resolve_left ha
    have hd := dvd_sub (hs n₀ hn₀).2.2 (hs n hn).2.2
    convert hd using 1
    ring
  · rw [not_nonempty_iff_eq_empty.mp he,sum_empty]
    positivity

end OrdinaryCorrelations.ArithmeticSaving

end

end OAI
