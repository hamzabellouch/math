import OAI.NumberTheory.JointDickman.Analysis.MellinSieveLevel

namespace OAI

/-! # Sparse prime Mellin sampling in polynomial frequency ranges -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

/-- An unconditional prime-density sampling bound. The sparse sample
exponent may depend on the fixed polynomial frequency range. -/
theorem sparse_prime_mellin_sampling (B : ℝ) (hB : 1 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ q : ℕ in atTop, ∀ (N : ℝ) (Q : Finset ℕ) (S : Finset ℝ),
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      (S.card:ℝ) ≤ (q:ℝ)^κ →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
        C*N/Real.log N * ∑ p ∈ Q, ‖a p‖^2 := by
  obtain ⟨C,A,δ,V,hC,hA,hδ,hδ1,hbound⟩ := mellin_prime_sampling_arithmetic B hB
  obtain ⟨D,hD,hprod⟩ := prime_survival_eventually_le
  let κ : ℝ := min (1/8) δ
  have hκ : 0 < κ := lt_min (by norm_num) hδ
  have hκ8 : κ ≤ 1/8 := min_le_left _ _
  have hκδ : κ ≤ δ := min_le_right _ _
  have hκ1 : κ ≤ 1 := hκ8.trans (by norm_num)
  let E : ℝ := 8*(32*C*(22*D/κ)+1)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E,κ,hE,hκ,?_⟩
  have hlevel := tendsto_natCast_atTop_atTop.eventually (mellin_small_sieve_level hκ hκ1)
  have herr := tendsto_natCast_atTop_atTop.eventually
    (mellin_sieve_remainder_absorption A hA.le hδ hκ8 hκδ)
  have hp := ((mellin_sieve_level_tendsto hκ).comp tendsto_natCast_atTop_atTop).eventually hprod
  have hv := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop V
  filter_upwards [eventually_ge_atTop 16,hlevel,herr,hp,hv] with q hq hlevel herr hp hv
  simp only [Function.comp_apply, Real.rpow_ofNat] at hv
  simp only [Function.comp_apply, Nat.floor_natCast] at hp
  intro N Q S hNlo hNhi hQ hsep hdiam hcard a
  let Z := ⌊(q:ℝ)^κ⌋₊
  let P := (Icc 2 Z).filter Nat.Prime
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN1 : 1 < N := (one_lt_pow₀ (by linarith : (1:ℝ) < q) (by norm_num : 10 ≠ 0)).trans_le hNlo
  have hN0 : 0 < N := by linarith
  have hZ : 2 ≤ Z := hlevel.1
  have hZq : Z ≤ q := by exact_mod_cast hlevel.2.1
  have hP : ∀ p ∈ P, p.Prime ∧ p ≤ Z := by
    intro p hp
    exact ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).2⟩
  have hQN : ∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N := by
    intro p hp
    have hpow : (q:ℝ) < (q:ℝ)^10 := by
      have hh := pow_le_pow_right₀ hq1 (show 2 ≤ 10 by norm_num)
      nlinarith
    have hZp : (Z:ℝ) < p := hlevel.2.1.trans_lt (hpow.trans_le (hNlo.trans (hQ p hp).2.1))
    exact ⟨(hQ p hp).1, by exact_mod_cast hZp, (hQ p hp).2⟩
  have hs := hbound q Z P Q N S hq hZ hZq hv hNlo hNhi hP hQN hsep hdiam a
  have herror := herr N (↑(Z+1)) S.card (↑(Nat.log 2 (q^3)+1)) hNlo hNhi
    (by positivity) hlevel.2.2.1 (by positivity) hcard (by positivity)
    (mellin_dyadic_count_le (by omega))
  have hlogZ : (κ/22)*Real.log N ≤ Real.log (Z:ℝ) := by
    have hl := Real.log_le_log hN0 hNhi
    rw [Real.log_pow] at hl
    have hzlog : (κ/2)*Real.log (q:ℝ) ≤ Real.log (Z:ℝ) := hlevel.2.2.2
    norm_num only [Nat.cast_ofNat] at hl
    nlinarith
  have hlogZ0 : 0 < Real.log (Z:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hlogN0 := Real.log_pos hN1
  have hPbound : (∏ p ∈ P, (1-1/(p:ℝ))) ≤ (22*D/κ)/Real.log N := by
    have hp' : (∏ p ∈ P, (1-1/(p:ℝ))) ≤ D/Real.log (Z:ℝ) := by
      simpa only [Nat.floor_natCast] using hp
    apply hp'.trans
    apply (div_le_div_iff₀ hlogZ0 hlogN0).mpr
    have hh := mul_le_mul_of_nonneg_left hlogZ (show 0 ≤ 22*D/κ by positivity)
    have he : (22*D/κ)*((κ/22)*Real.log N) = D*Real.log N := by field_simp
    rw [he] at hh
    exact hh
  apply hs.trans
  have hmain : 32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) ≤ 32*C*(22*D/κ)*(N/Real.log N) := by
    apply (mul_le_mul_of_nonneg_left hPbound (by positivity : 0 ≤ 32*C*N)).trans_eq
    ring
  have htotal : 8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
      (6*(q:ℝ)^9+(Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card) ≤ E*N/Real.log N := by
    dsimp only [E]
    calc
      _ ≤ 8*(32*C*(22*D/κ)*(N/Real.log N)+N/Real.log N) :=
        mul_le_mul_of_nonneg_left (add_le_add hmain herror) (by norm_num)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right htotal (sum_nonneg (fun _ _ => sq_nonneg _))

end JointDickman

end OAI
