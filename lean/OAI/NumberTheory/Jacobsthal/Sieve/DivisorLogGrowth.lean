import OAI.NumberTheory.Jacobsthal.Estimates.UnitCyclicBounds
import OAI.NumberTheory.Jacobsthal.Primes.PrimePowerGrowth

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosDivisorBounds

theorem prime_factor_product (n : ℕ) (hn : n ≠ 0) (eps : ℝ) :
    (∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) = (n : ℝ)^eps := by
  calc
    _ = ∏ p ∈ n.primeFactors, ((p : ℝ)^(n.factorization p))^eps := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
        ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      congr 1
      ring
    _ = (∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p))^eps :=
      Real.finsetProd_rpow _ _ (fun p _ => by positivity) eps
    _ = _ := by
      have h : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ)^(n.factorization p) := by
        exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
      rw [← h]

theorem small_factor_product (s : Finset ℕ) (P : ℕ) {B : ℝ} (hB : 1 ≤ B) :
    (∏ p ∈ s, if p < P then B else 1) ≤ B^P := by
  classical
  have hcard : (s.filter (fun p => p < P)).card ≤ P := by
    calc
      _ ≤ (Finset.range P).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = P := Finset.card_range P
  rw [Finset.prod_ite]
  simpa using pow_le_pow_right₀ hB hcard

theorem divisor_subpower {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ A*(n : ℝ)^eps := by
  classical
  obtain ⟨B,hB,hsmall⟩ := local_power_bound heps
  obtain ⟨P,hlarge⟩ := large_prime_power_bound heps
  refine ⟨B^P, pow_pos (by linarith) _, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hcard : (n.divisors.card : ℝ) =
      ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
    exact_mod_cast Nat.card_divisors hn0
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ)+1 ≤
        (if p < P then B else 1)*((p : ℝ)^eps)^(n.factorization p) := by
    by_cases h : p < P
    · simpa only [h,ite_true] using hsmall p (Nat.prime_of_mem_primeFactors hp).two_le (n.factorization p)
    · simpa only [h,ite_false,one_mul] using hlarge p (by omega) (n.factorization p)
  calc
    _ = _ := hcard
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < P then B else 1)*((p : ℝ)^eps)^(n.factorization p) :=
      Finset.prod_le_prod₀ (fun p _ => by positivity) hlocal
    _ = (∏ p ∈ n.primeFactors, if p < P then B else 1) *
        (∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) := Finset.prod_mul_distrib
    _ ≤ B^P*(∏ p ∈ n.primeFactors, ((p : ℝ)^eps)^(n.factorization p)) :=
      mul_le_mul_of_nonneg_right (small_factor_product _ P hB) (by positivity)
    _ = _ := by rw [prime_factor_product n hn0 eps]

theorem divisor_power_subpower (C : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ)^C ≤ A*(n : ℝ)^eps := by
  let delta : ℝ := eps/((C : ℝ)+1)
  have hden : 0 < (C : ℝ)+1 := by positivity
  have hd : 0 < delta := div_pos heps hden
  obtain ⟨A,hA,hbound⟩ := divisor_subpower hd
  refine ⟨A^C,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hde : delta*(C : ℝ) ≤ eps := by
    have he : delta*((C : ℝ)+1) = eps := by dsimp [delta]; field_simp
    nlinarith

  calc
    _ ≤ (A*(n : ℝ)^delta)^C := pow_le_pow_left₀ (Nat.cast_nonneg _) (hbound n hn) C
    _ = A^C*(n : ℝ)^(delta*(C : ℝ)) := by
      rw [mul_pow,Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hde) (pow_nonneg hA.le _)

end ErdosDivisorBounds

end

section

namespace ErdosUniformMobiusRemainder

theorem totient_ratio_le_divisors (H : ℕ) (hH : 1 ≤ H) :
    (H : ℝ)/(H.totient : ℝ) ≤ (H.divisors.card : ℝ) := by
  have hphi : 0 < H.totient := Nat.totient_pos.mpr hH
  have hs : H ≤ H.divisors.card*H.totient := by
    calc
      _ = ∑ d ∈ H.divisors,d.totient := (Nat.sum_totient H).symm
      _ ≤ ∑ _d ∈ H.divisors,H.totient := Finset.sum_le_sum (fun d hd =>
        Nat.le_of_dvd hphi (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  apply (div_le_iff₀ (show (0 : ℝ) < H.totient by exact_mod_cast hphi)).mpr
  exact_mod_cast hs

theorem divisor_totient_quarter : ∃ C : ℝ,0 < C ∧ ∀ H : ℕ,1 ≤ H →
    (H.divisors.card : ℝ)*(H : ℝ)/(H.totient : ℝ) ≤ C*(H : ℝ)^((1 : ℝ)/4) := by
  obtain ⟨C,hC,hb⟩ := ErdosDivisorBounds.divisor_power_subpower 2 (by norm_num : (0 : ℝ) < 1/4)
  refine ⟨C,hC,?_⟩
  intro H hH
  calc
    _ = (H.divisors.card : ℝ)*((H : ℝ)/(H.totient : ℝ)) := by ring
    _ ≤ (H.divisors.card : ℝ)*(H.divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_left (totient_ratio_le_divisors H hH) (Nat.cast_nonneg _)
    _ = (H.divisors.card : ℝ)^2 := by ring
    _ ≤ _ := hb H hH

theorem divisor_totient_length_bound : ∃ C : ℝ,0 < C ∧ ∀ (H : ℕ) (Y : ℝ),
    1 ≤ H → (H : ℝ) ≤ Y →
      (H.divisors.card : ℝ)*(H : ℝ)/(Y*(H.totient : ℝ)) ≤ C/Y^((1 : ℝ)/2) := by
  obtain ⟨C,hC,hb⟩ := divisor_totient_quarter
  refine ⟨C,hC,?_⟩
  intro H Y hH hHY
  have hY1 : 1 ≤ Y := (show (1 : ℝ) ≤ H by exact_mod_cast hH).trans hHY
  have hY : 0 < Y := by linarith
  have hpow : (H : ℝ)^((1 : ℝ)/4) ≤ Y^((1 : ℝ)/2) :=
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hHY (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  have hroot : 0 < Y^((1 : ℝ)/2) := Real.rpow_pos_of_pos hY _
  have hrootSq : Y^((1 : ℝ)/2)*Y^((1 : ℝ)/2)=Y := by
    rw [← Real.rpow_add hY]
    norm_num
  calc
    _ = ((H.divisors.card : ℝ)*(H : ℝ)/(H.totient : ℝ))/Y := by ring
    _ ≤ (C*(H : ℝ)^((1 : ℝ)/4))/Y := div_le_div_of_nonneg_right (hb H hH) hY.le
    _ ≤ (C*Y^((1 : ℝ)/2))/Y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hY.le
    _ = _ := by
      apply (div_eq_div_iff hY.ne' hroot.ne').mpr
      rw [mul_assoc,hrootSq]

end ErdosUniformMobiusRemainder

end

section

namespace ErdosHyperbolaWeighted

theorem divisor_log_square_subpower (C : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      (N.divisors.card : ℝ)^C*(Real.log (2*(N : ℝ)))^2 ≤ A*(N : ℝ)^eps := by
  let alpha := eps/2
  let beta := eps/4
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hb : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨A, hA, hdiv⟩ := ErdosDivisorBounds.divisor_power_subpower C ha
  let L := (2 : ℝ)^beta/beta
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨A*L^2, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log (2*(N : ℝ)) := Real.log_nonneg (by linarith)
  have hlogbound : (Real.log (2*(N : ℝ)))^2 ≤ L^2*(N : ℝ)^(beta*2) := by
    calc
      _ ≤ (L*(N : ℝ)^beta)^2 := pow_le_pow_left₀ hlog (log_two_mul_le_power hb hNpos) 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
        norm_num
  calc
    _ ≤ (A*(N : ℝ)^alpha)*(L^2*(N : ℝ)^(beta*2)) :=
      mul_le_mul (hdiv N hN) hlogbound (sq_nonneg _) (by positivity)
    _ = A*L^2*(N : ℝ)^eps := by
      have he : alpha+beta*2 = eps := by dsimp [alpha,beta]; ring
      rw [← he, Real.rpow_add hNpos]
      ring

end ErdosHyperbolaWeighted

end

end Erdos970

end OAI
