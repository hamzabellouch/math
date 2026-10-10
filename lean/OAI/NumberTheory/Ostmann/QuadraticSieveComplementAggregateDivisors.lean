import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped ArithmeticFunction.Moebius

private theorem complement_range_radical {C ε E : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hN : 0 < N) (hE : 0 ≤ E) :
    Real.sqrt (C*(N:ℝ)^(2*ε)*E*E) = Real.sqrt C*(N:ℝ)^ε*E := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hp : (N:ℝ)^(2*ε) = ((N:ℝ)^ε)^2 := by
    rw [two_mul,Real.rpow_add hNr]
    ring
  have he : C*(N:ℝ)^(2*ε)*E*E = (Real.sqrt C*(N:ℝ)^ε*E)^2 := by
    rw [hp,mul_pow,mul_pow,Real.sq_sqrt hC]
    ring
  rw [he,Real.sqrt_sq (by positivity)]

theorem complement_divisor_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T x H A : ℝ) (K j Δ r N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℂ),
      0 < M → 1 ≤ T → 0 ≤ x → 0 ≤ H → 0 ≤ A → 0 < Δ →
      r ∈ (2*Δ).divisors → 0 < N → S ⊆ oddSquarefreeUpTo N →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        H*(x+(N:ℝ)/q)) →
      (∀ d, ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d, ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 →
        complementWindowLower M T v < (r*d:ℕ)) →
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g d v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)‖ ≤
        (Nat.log 2 (N^2)+2:ℕ)*(C*A*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*
          (Real.sqrt (M/(2^j:ℕ))*x+(32*(Δ:ℝ)*T)*N) := by
  classical
  obtain ⟨Cr,hCr,hrange⟩ := complement_active_range_bound (2*ε) (by positivity)
  obtain ⟨Cb,hCb,hboundary⟩ := complement_active_boundary_bound ε hε
  let C := Cb+2*Real.sqrt Cr
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M T x H A K j Δ r N S a g hM hT hx hH hA hΔ hr hN hS hnorm hg hsupp
  have hrp : (0:ℝ) < r := by exact_mod_cast Nat.pos_of_mem_divisors hr
  have hE := coefficientEnergy_nonneg S a
  let F : ℕ → ℂ := fun d => ∑ v ∈ binarySquarefreeRows K j,
    (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g d v*
      coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)
  let G : ℝ := Real.sqrt (M/(2^j:ℕ))*x+(32*(Δ:ℝ)*T)*N
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let R : ℝ := (C*A*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*G
  have hfirst : ‖F 1‖ ≤ R := by
    have hn1 := hnorm 1 (by norm_num)
    simp only [Nat.div_one, Nat.cast_one,div_one] at hn1
    have hb := hboundary M T x H A K j Δ r N S a (g 1) hM hT hx hH hA hΔ hr hN hS hn1
      (hg 1) (hsupp 1)
    have hG4 : Real.sqrt (M/(2^j:ℕ))*x+(4*(Δ:ℝ)*T)*N ≤ G := by
      dsimp [G]
      nlinarith [show 0 ≤ (Δ:ℝ)*T*(N:ℝ) by positivity]
    have hc : Cb ≤ C := by dsimp [C]; linarith [Real.sqrt_nonneg Cr]
    have hb' : ‖F 1‖ ≤ (A*Cb*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*
        (Real.sqrt (M/(2^j:ℕ))*x+(4*(Δ:ℝ)*T)*N) := by
      simpa only [F,Nat.cast_one] using hb
    refine hb'.trans ?_
    calc
      _ ≤ (A*Cb*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*G :=
        mul_le_mul_of_nonneg_left hG4 (by positivity)
      _ ≤ R := by
        have hh := mul_le_mul_of_nonneg_right hc
          (show 0 ≤ A*H/(r:ℝ)*(N:ℝ)^ε*coefficientEnergy S a*G by positivity)
        dsimp [R]
        convert hh using 1 <;> ring
  have hblocks : ∀ k ∈ Finset.range (Nat.log 2 (N^2)+1),
      ‖∑ d ∈ aggregateDivisorBlock (N^2) k, F d‖ ≤ R := by
    intro k hk
    let g' : ℕ → ℕ → ℂ := fun d v => if d ≤ N^2 then g d v else 0
    have hg' : ∀ d ∈ Finset.Ioc (2^k) (2*2^k), ∀ v ∈ binarySquarefreeRows K j, ‖g' d v‖ ≤ A := by
      intro d hd v hv
      dsimp [g']
      split_ifs
      · exact hg d v hv
      · simpa using hA
    have hs' : ∀ d ∈ Finset.Ioc (2^k) (2*2^k), ∀ v ∈ binarySquarefreeRows K j,
        g' d v ≠ 0 → complementWindowLower M T v < (r*d:ℕ) := by
      intro d hd v hv hnz
      by_cases hdN : d ≤ N^2
      · exact hsupp d v hv (by simpa [g',hdN] using hnz)
      · exact False.elim (hnz (by simp [g',hdN]))
    have hh := hrange M T x H A K j Δ r (2^k) N S a g' hM hT hx hH hA hΔ hr
      (by positivity) hN hS hnorm hg' hs'
    rw [complement_range_radical hCr.le hN hE] at hh
    have heq : (∑ d ∈ aggregateDivisorBlock (N^2) k, F d) =
        ∑ d ∈ Finset.Ioc (2^k) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
          (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g' d v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ) := by
      rw [aggregateDivisorBlock,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdN : d ≤ N^2 <;> simp [g',F,hdN]
    rw [heq]
    refine hh.trans ?_
    have hc : 2*Real.sqrt Cr ≤ C := by dsimp [C]; linarith
    have hb := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ A*H/(r:ℝ)*(N:ℝ)^ε*coefficientEnergy S a*G by positivity)
    dsimp [R,G] at hb ⊢
    convert hb using 1 <;> ring
  have hh := norm_sum_Icc_one_le_boundary_dyadic (N^2) (by positivity) F R hfirst hblocks
  change ‖∑ d ∈ Finset.Icc 1 (N^2), F d‖ ≤ _
  refine hh.trans_eq ?_
  dsimp [R,G]
  ring

end Ostmann.QuadraticSieve

end

end OAI
