import OAI.NumberTheory.JointDickman.Amplification.NearCofactorMean

namespace OAI

/-! # Near-zero cancellation on the literal cofactor window -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology ComplexConjugate

/-- Prefix cancellation on the near-zero frequency range passes to the
actual reciprocal-count cofactor by finite partial summation. -/
theorem near_zero_count_window : ∃ C : ℝ, ∃ K : ℕ, 0 < C ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → K ≤ ⌊(N:ℝ)/a⌋₊ →
    ∀ F : ℕ → ℂ, F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    (∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log (⌊(N:ℝ)/a⌋₊:ℝ)))) →
    squaredDistance F (mrtArchimedeanTwist 0) ⌊(2*N:ℝ)/a⌋₊ +
      (∑ p ∈ P, 1/(p:ℝ)) ≤ Real.log (Real.log (⌊(N:ℝ)/a⌋₊:ℝ))/8 →
    ∀ t : ℝ, |t| ≤ (Real.log (⌊(N:ℝ)/a⌋₊:ℝ))^((1:ℝ)/16) →
    ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤
      5*(2/(1+|t|)+C*(Real.log (⌊(N:ℝ)/a⌋₊:ℝ))^(-(1:ℝ)/16)) := by
  obtain ⟨C,hC,hmean⟩ := near_zero_count_prefix
  obtain ⟨K,hK⟩ := eventually_atTop.mp hmean
  refine ⟨C,max K 2,hC,le_max_right _ _,?_⟩
  intro N a ha hm F hF1 hFm hFb Q P hQ hP hcut hdist t ht
  let m := ⌊(N:ℝ)/a⌋₊
  let n := ⌊(2*N:ℝ)/a⌋₊
  have hm2 : 2 ≤ m := (le_max_right K 2).trans hm
  have hmK : K ≤ m := (le_max_left K 2).trans hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hx : 2 ≤ (N:ℝ)/a := (by exact_mod_cast hm2 : (2:ℝ) ≤ m).trans
    (Nat.floor_le (by positivity))
  apply mrt_cofactor_bound_of_prefix P (mrtMissingCoefficient F Q) N ha hx t (by positivity)
  intro k hk
  change k ∈ Icc m n at hk
  have hmk := (mem_Icc.mp hk).1
  have hkn := (mem_Icc.mp hk).2
  have hlogk : Real.log (m:ℝ) ≤ Real.log (k:ℝ) :=
    Real.log_le_log hm0 (by exact_mod_cast hmk)
  have hloglog : Real.log (Real.log (m:ℝ)) ≤ Real.log (Real.log (k:ℝ)) :=
    Real.log_le_log hlog hlogk
  have hcutk : ∀ p ∈ Q, (p:ℝ) ≤ Real.exp (Real.sqrt (Real.log (k:ℝ))) := by
    intro p hp
    exact (hcut p hp).trans (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlogk))
  have hdk : squaredDistance F (mrtArchimedeanTwist 0) k + (∑ p ∈ P, 1/(p:ℝ)) ≤
      Real.log (Real.log (k:ℝ))/8 := by
    have hdmono : squaredDistance F (mrtArchimedeanTwist 0) k ≤
        squaredDistance F (mrtArchimedeanTwist 0) n := by
      unfold squaredDistance
      apply sum_le_sum_of_subset_of_nonneg (halasz_prime_cutoff_subset hkn)
      intro p hp _
      have hprime := (mem_filter.mp hp).2
      have hr := (Complex.re_le_norm (F p)).trans (hFb p hprime.pos)
      simpa only [mrtArchimedeanTwist, zero_mul, Complex.ofReal_zero,
        Complex.exp_zero, map_one, mul_one] using
        div_nonneg (sub_nonneg.mpr hr) (Nat.cast_nonneg p)
    linarith
  have htk : |t| ≤ (Real.log (k:ℝ))^((1:ℝ)/16) := ht.trans
    (Real.rpow_le_rpow hlog.le hlogk (by norm_num))
  have hh := hK k (hmK.trans hmk) F hF1 hFm hFb Q P hQ hP hcutk hdk t htk
  apply hh.trans
  have herr : (Real.log (k:ℝ))^(-(1:ℝ)/16) ≤ (Real.log (m:ℝ))^(-(1:ℝ)/16) :=
    Real.rpow_le_rpow_of_nonpos hlog hlogk (by norm_num)
  exact mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left herr hC.le)) (Nat.cast_nonneg k)

end JointDickman

end OAI
