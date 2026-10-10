import OAI.NumberTheory.Jacobsthal.Harmonic.SharpCharacterLogPower

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def principalDifference (q : ℕ) [NeZero q] (n : ℕ) : ℂ :=
  (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)-
    (ArithmeticFunction.vonMangoldt n:ℂ)

lemma principalDifference_norm_le (q : ℕ) [NeZero q] (n : ℕ) :
    ‖principalDifference q n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  unfold principalDifference
  by_cases hu : IsUnit (n:ZMod q)
  · rw [MulChar.one_apply hu,one_mul,sub_self,norm_zero]
    exact ArithmeticFunction.vonMangoldt_nonneg
  · rw [MulChar.map_nonunit _ hu,zero_mul,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

lemma excluded_primePower_dvd_power (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hLambda : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hu : ¬IsUnit (n:ZMod q)) : n ∣ q^(Nat.log 2 N) := by
  obtain ⟨p,k,hp,hk,he⟩ := (isPrimePow_nat_iff n).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda)
  have hpq : p ∣ q := by
    by_contra h
    apply hu
    rw [← he,Nat.cast_pow]
    exact ((ZMod.isUnit_prime_iff_not_dvd hp).mpr h).pow k
  have h2 : 2^k ≤ n := by rw [← he]; gcongr; exact hp.two_le
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) (h2.trans hn)
  rw [← he]
  exact (pow_dvd_pow p hkN).trans (pow_dvd_pow_of_dvd hpq _)

lemma principalDifference_eq_zero_of_not_dvd (q : ℕ) [NeZero q] {N n : ℕ}
    (hn : n ≤ N) (hnd : ¬n ∣ q^(Nat.log 2 N)) : principalDifference q n = 0 := by
  by_cases hl : ArithmeticFunction.vonMangoldt n = 0
  · simp only [principalDifference,hl,Complex.ofReal_zero,mul_zero,sub_self]
  · by_cases hu : IsUnit (n:ZMod q)
    · simp only [principalDifference,MulChar.one_apply hu,one_mul,sub_self]
    · exact (hnd (excluded_primePower_dvd_power q hn hl hu)).elim

theorem norm_principal_sharp_difference (q : ℕ) [NeZero q] (X : ℝ) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Nat.log 2 ⌊X⌋₊:ℝ)*Real.log (q:ℝ) := by
  let K : ℕ := Nat.log 2 ⌊X⌋₊
  let N := Finset.range (⌊X⌋₊+1)
  let D := (q^K).divisors
  let S := N ∩ D
  have hqpow : q^K ≠ 0 := pow_ne_zero _ (NeZero.ne q)
  have hsub : S ⊆ N := Finset.inter_subset_left
  have hsum : (∑ n ∈ S, principalDifference q n) = ∑ n ∈ N, principalDifference q n := by
    apply Finset.sum_subset hsub
    intro n hn hnS
    have hn' : n ≤ ⌊X⌋₊ := by simpa only [N,Finset.mem_range,Nat.lt_add_one_iff] using hn
    apply principalDifference_eq_zero_of_not_dvd q hn'
    intro hd
    apply hnS
    exact Finset.mem_inter.mpr ⟨hn,Nat.mem_divisors.mpr ⟨hd,hqpow⟩⟩
  unfold sharpSum
  rw [← Finset.sum_sub_distrib]
  change ‖∑ n ∈ N, principalDifference q n‖ ≤ (K:ℝ)*Real.log (q:ℝ)
  rw [← hsum]
  calc
    _ ≤ ∑ n ∈ S, ‖principalDifference q n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => principalDifference_norm_le q n)
    _ ≤ ∑ n ∈ D, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log ((q^K:ℕ):ℝ) := ArithmeticFunction.vonMangoldt_sum
    _ = _ := by rw [Nat.cast_pow,Real.log_pow]

lemma natLog_floor_le_realLog {X : ℝ} (hX : 1 ≤ X) :
    (Nat.log 2 ⌊X⌋₊:ℝ) ≤ Real.log X/Real.log 2 := by
  have hfloor : ⌊X⌋₊ ≠ 0 := by
    intro hz
    have h := Nat.lt_floor_add_one X
    rw [hz] at h
    norm_num at h
    linarith
  have hNat := Nat.pow_log_le_self 2 hfloor
  have hp : (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ X :=
    (show (2:ℝ)^(Nat.log 2 ⌊X⌋₊) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hNat).trans
      (Nat.floor_le (by linarith))
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 ⌊X⌋₊)) hp
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hlog

theorem norm_principal_sharp_difference_real (q : ℕ) [NeZero q] {X : ℝ} (hX : 1 ≤ X) :
    ‖sharpSum (fun n:ℕ => (1:DirichletCharacter ℂ q) n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
      sharpSum (fun n:ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
      (Real.log X/Real.log 2)*Real.log (q:ℝ) := by
  apply (norm_principal_sharp_difference q X).trans
  exact mul_le_mul_of_nonneg_right (natLog_floor_le_realLog hX)
    (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
