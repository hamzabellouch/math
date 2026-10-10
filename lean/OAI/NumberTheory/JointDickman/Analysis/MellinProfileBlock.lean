import OAI.NumberTheory.JointDickman.Analysis.MellinWeightedLogPhase

namespace OAI

/-! # A uniform logarithmic block bound for the Mellin profile -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma mellin_sum_Icc_split (f : ℤ → ℂ) {L K R : ℤ} (hLK : L ≤ K) (hKR : K < R) :
    (∑ n ∈ Icc L R, f n) = (∑ n ∈ Icc L K, f n)+(∑ n ∈ Icc (K+1) R, f n) := by
  have he : Icc L R = Icc L K ∪ Icc (K+1) R := by
    ext n
    simp only [mem_Icc, mem_union]
    omega
  rw [he, sum_union]
  apply disjoint_left.mpr
  intro n hn hn'
  simp only [mem_Icc] at hn hn'
  omega

lemma mellin_profile_crossing_bound {N : ℝ} (hN : 1 ≤ N) (t : ℝ) (L R : ℤ)
    (hL : 0 < L) (hLN : (L:ℝ) ≤ N) (hNR : N < (R:ℝ))
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ A B : ℤ, L ≤ A → B ≤ R →
      ‖∑ n ∈ Icc A B, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 6*D := by
  let K : ℤ := ⌊N⌋
  have hLK : L ≤ K := Int.le_floor.mpr hLN
  have hKN : (K:ℝ) ≤ N := Int.floor_le N
  have hNK : N < (K:ℝ)+1 := Int.lt_floor_add_one N
  have hKR : K < R := by exact_mod_cast hKN.trans_lt hNR
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hl := mellinSieveFunction_left_sum hN0 t L K hL hLK hKN hD
    (fun V _ hVK => hpartial L V le_rfl (hVK.trans hKR.le))
  have hr := mellinSieveFunction_right_sum hN0 t (K+1) R (by omega)
    (by exact_mod_cast hNK.le) hD (fun V _ hVR => hpartial (K+1) V (by omega) hVR)
  have hlb : 2*D*((K:ℝ)+1)/N ≤ 4*D := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith
  have hrb : N^3*D*((K+1:ℤ):ℝ)^(-3:ℝ) ≤ D := by
    have hK0 : (0:ℝ) < (K+1:ℤ) := by exact_mod_cast (show 0 < K+1 by omega)
    have hK : N ≤ ((K+1:ℤ):ℝ) := by exact_mod_cast hNK.le
    rw [Real.rpow_neg hK0.le, Real.rpow_ofNat]
    have hc : N^3*((((K+1:ℤ):ℝ)^3)⁻¹) ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (pow_pos hK0 3)]
      exact pow_le_pow_left₀ hN0.le hK 3
    nlinarith
  rw [mellin_sum_Icc_split _ hLK hKR]
  exact (norm_add_le _ _).trans (by linarith [hl,hr])

lemma mellin_profile_block_bound {N U A δ : ℝ} (hN : 1 ≤ N) (hU : 1 ≤ U)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) (L R : ℤ)
    (hUL : U ≤ (L:ℝ)) (hRU : (R:ℝ) ≤ 2*U)
    (hpartial : ∀ l r : ℤ, L ≤ l → r ≤ R →
      ‖∑ n ∈ Icc l r, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤ A*U^(1-δ)) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 6*A*N^(1-δ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hL : 0 < L := by exact_mod_cast (hU0.trans_le hUL)
  have hD : 0 ≤ A*U^(1-δ) := by positivity
  by_cases hLR : L ≤ R
  swap
  · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hLR), sum_empty, norm_zero]
    positivity
  by_cases hRN : (R:ℝ) ≤ N
  · have hUN : U ≤ N := hUL.trans ((by exact_mod_cast hLR : (L:ℝ) ≤ R).trans hRN)
    have hh := mellinSieveFunction_left_sum hN0 t L R hL hLR hRN hD
      (fun V _ hVR => hpartial L V le_rfl hVR)
    have hp : U^(1-δ) ≤ N^(1-δ) := Real.rpow_le_rpow hU0.le hUN (by linarith)
    apply hh.trans
    apply (div_le_iff₀ hN0).mpr
    have hR : (R:ℝ)+1 ≤ 3*U := by linarith
    calc
      2*(A*U^(1-δ))*((R:ℝ)+1) ≤ 6*A*U^(1-δ)*U := by nlinarith [mul_nonneg hA (Real.rpow_nonneg hU0.le (1-δ))]
      _ ≤ 6*A*N^(1-δ)*N := mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hUN hU0.le (by positivity)
  by_cases hNL : N ≤ (L:ℝ)
  · have hh := mellinSieveFunction_right_sum hN0 t L R hL hNL hD
      (fun V _ hVR => hpartial L V le_rfl hVR)
    have hL0 : (0:ℝ) < L := by exact_mod_cast hL
    have hc : N^3*(L:ℝ)^(-3:ℝ) ≤ 1 := by
      rw [Real.rpow_neg hL0.le, Real.rpow_ofNat, ← div_eq_mul_inv,
        div_le_one (pow_pos hL0 3)]
      exact pow_le_pow_left₀ hN0.le hNL 3
    have hcore : N^3*(U^(1-δ)*(L:ℝ)^(-3:ℝ)) ≤ N^(1-δ) := by
      by_cases hUN : U ≤ N
      · have hp := Real.rpow_le_rpow hU0.le hUN (show 0 ≤ 1-δ by linarith)
        calc
          _ = (N^3*(L:ℝ)^(-3:ℝ))*U^(1-δ) := by ring
          _ ≤ 1*N^(1-δ) := mul_le_mul hc hp (Real.rpow_nonneg hU0.le _) (by norm_num)
          _ = _ := one_mul _
      · have hNU : N ≤ U := le_of_not_ge hUN
        calc
          _ ≤ N^3*(U^(1-δ)*U^(-3:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN0.le 3)
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hU0.le _)
            exact Real.rpow_le_rpow_of_nonpos hU0 hUL (by norm_num)
          _ = N^3*U^(-2-δ) := by rw [← Real.rpow_add hU0]; congr 2; ring
          _ ≤ N^3*N^(-2-δ) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hN0 hNU (by linarith)) (by positivity)
          _ = N^(1-δ) := by rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN0]; congr 1; norm_num; ring
    have hb : N^3*(A*U^(1-δ))*(L:ℝ)^(-3:ℝ) ≤ A*N^(1-δ) := by
      calc
        _ = A*(N^3*(U^(1-δ)*(L:ℝ)^(-3:ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcore hA
    exact hh.trans (hb.trans (by nlinarith [mul_nonneg hA (Real.rpow_nonneg hN0.le (1-δ))]))
  · have hLN : (L:ℝ) ≤ N := le_of_not_ge hNL
    have hUN := hUL.trans hLN
    have hh := mellin_profile_crossing_bound hN t L R hL hLN (lt_of_not_ge hRN) hD hpartial
    exact hh.trans (by
      have hp := Real.rpow_le_rpow hU0.le hUN (show 0 ≤ 1-δ by linarith)
      calc
        6*(A*U^(1-δ)) = (6*A)*U^(1-δ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity))

/-- A fixed polynomial frequency range has a positive power saving for
all the scaled profile blocks, uniformly in the profile's maximum. -/
theorem mellin_profile_block_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (N t : ℝ) (L R : ℤ), 1 ≤ N →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ A*N^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := angular_log_phase_uniform B hB
  let ε : ℝ := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  refine ⟨6*A,ε,by positivity,hε,hε1,?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with U hbound hU
  intro N t L R hN hlo hhi hL hR
  have hh := mellin_profile_block_bound hN hU hA.le hε hε1 t L R hL hR (by
    intro l r hLl hrR
    apply (hbound t l r hlo hhi (hL.trans (by exact_mod_cast hLl))
      ((by exact_mod_cast hrR : (r:ℝ) ≤ R).trans hR)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) hA.le)
  simpa only [mul_assoc] using hh

theorem mellin_dilated_profile_block_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (N d t : ℝ) (L R : ℤ), 0 < d → d ≤ N →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, mellinSieveFunction N t (d*n)‖ ≤ A*(N/d)^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hδ1,hbound⟩ := mellin_profile_block_uniform B hB
  refine ⟨A,δ,hA,hδ,hδ1,?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with U hbound hU
  intro N d t L R hd hdN hlo hhi hL hR
  have hN : 0 < N := hd.trans_le hdN
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t (d*n)) =
      Complex.exp (((-Real.log d*t:ℝ):ℂ)*Complex.I)*
        ∑ n ∈ Icc L R, mellinSieveFunction (N/d) t n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    exact mellinSieveFunction_dilate hN hd
      (lt_of_lt_of_le zero_lt_one (hU.trans (hL.trans (by exact_mod_cast (mem_Icc.mp hn).1)))) t
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact hbound (N/d) t L R ((one_le_div hd).mpr hdN) hlo hhi hL hR

end JointDickman

end OAI
