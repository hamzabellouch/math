import OAI.NumberTheory.JointDickman.Arithmetic.PrimeRationalBilinear

namespace OAI

/-! # Natural-index form of the prime rectangle estimate -/
namespace JointDickman
open Finset

lemma sum_Ioc_nat_as_int {R : Type*} [AddCommMonoid R] (F : ℤ → R) (Z K : ℕ) :
    (∑ n ∈ Ioc Z K, F n) = ∑ n ∈ Ioc (Z:ℤ) K, F n := by
  apply sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    simp only [mem_Ioc] at hn ⊢
    exact_mod_cast hn
  · intro n hn m hm he
    exact_mod_cast he
  · intro n hn
    have hn0 : 0 ≤ n := (Int.natCast_nonneg Z).trans (mem_Ioc.mp hn).1.le
    refine ⟨n.toNat,?_,Int.toNat_of_nonneg hn0⟩
    simp only [mem_Ioc] at hn ⊢
    omega
  · intro n hn
    rfl

lemma prime_rectangle_nat_int (P : Finset ℕ) (b c : ℕ → ℂ)
    (θ : ℝ) (Z K : ℕ) (hZ : Z ≤ K) :
    (∑ p ∈ P, ∑ n ∈ Ioc Z K, b p*c n*additivePhase (θ*p*n)) =
      ∑ n ∈ Ico ((Z:ℤ)+1) ((Z:ℤ)+1+(K-Z:ℕ)), c n.toNat *
        ∑ p ∈ P, b p*additivePhase (θ*p*n) := by
  rw [sum_comm]
  have he : Ioc (Z:ℤ) K = Ico ((Z:ℤ)+1) ((Z:ℤ)+1+(K-Z:ℕ)) := by
    ext n
    simp only [mem_Ioc,mem_Ico]
    omega
  rw [←he,←sum_Ioc_nat_as_int]
  apply sum_congr rfl
  intro n hn
  simp only [Int.toNat_natCast,Int.cast_natCast,mul_sum]
  apply sum_congr rfl
  intro p hp
  ring

theorem natural_prime_rational_rectangle_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (Q U q a Z K : ℕ) (P : Finset ℕ) (b c : ℕ → ℂ),
    2 ≤ Q → 0 < q → a.Coprime q → Z ≤ K → K-Z ≤ U →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log Q) → (∀ n, ‖c n‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ n ∈ Ioc Z K, b p*c n*additivePhase ((a:ℝ)/q*p*n)‖^2 ≤
      C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 +
        Q*(U:ℝ)^2*Q*(1+Real.log q)/q + Q*U*Q + Q*U*q*(1+Real.log Q)) := by
  obtain ⟨C,hC,hbound⟩ := prime_rational_bilinear_bound
  refine ⟨C,hC,?_⟩
  intro Q U q a Z K P b c hQ hq ha hZ hU hP hb hc
  rw [prime_rectangle_nat_int P b c ((a:ℝ)/q) Z K hZ]
  have h := hbound Q Q (K-Z) q a P b (fun n => c n.toNat) ((Z:ℤ)+1)
    hQ (by omega) hq ha hP
    (fun p hp r hr => (Nat.sub_le r p).trans (hP r hr).2) hb (fun n _ => hc n.toNat)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hUR : ((K-Z:ℕ):ℝ) ≤ U := by exact_mod_cast hU
  have hsq : (((K-Z:ℕ):ℝ))^2 ≤ (U:ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hUR 2
  gcongr

end JointDickman

end OAI
