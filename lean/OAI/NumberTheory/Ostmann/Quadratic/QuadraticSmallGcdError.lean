import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdTransform

namespace OAI

/-! # The three complete Poisson remainders at each small common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_pair_support_bound {N D : ℕ}
    (hD : D ∈ Finset.Icc 1 N) (v : ℕ → ℂ) (E : ℕ × ℕ → ℂ)
    {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ z ∈ quadraticGcdPairs N D, v z.1 ≠ 0 → v z.2 ≠ 0 → ‖E z‖ ≤ T) :
    ‖∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) * E z‖ ≤
      T * N * quadraticSieveEnergy N v := by
  let F (d : ℕ) (z : ℕ × ℕ) : ℂ := if d = D then E z else 0
  have he : quadraticGcdRemainder N v F =
      ∑ z ∈ quadraticGcdPairs N D, v z.1 * conj (v z.2) * E z := by
    unfold quadraticGcdRemainder F
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp [hD]
  rw [← he]
  apply quadratic_gcd_remainder_support_bound N v F hT
  intro d _ z hz hv hw
  dsimp [F]
  split_ifs with hd
  · subst d
    exact hE z hz hv hw
  · simpa only [norm_zero] using hT

theorem quadratic_small_gcd_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → 0 < D → D < R →
      ∀ J : ℝ, 1 ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticGcdMomentError M R K D J v‖ ≤
        C * (((M : ℝ) * R) ^ 6 / J ^ A) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_first_kernel_error A
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_first_second_kernel_error A
  obtain ⟨C₃, hC₃, hc₃⟩ := quadratic_small_pair_error A
  let C := 64 * C₁ + C₂ + C₃
  refine ⟨2 * C, by dsimp [C]; positivity, ?_⟩
  intro M R K D hM hR hD hDR J hJ hcut hK v hsupp
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hDRR : (D : ℝ) ≤ R := by exact_mod_cast hDR.le
  have hprod : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le hMR hRR
  have hMN : (0 : ℝ) < M := zero_lt_one.trans_le hMR
  have hRN : (0 : ℝ) < R := zero_lt_one.trans_le hRR
  have hRprod : (R : ℝ) ≤ (M : ℝ) * R := by nlinarith
  have hMprod : (M : ℝ) ≤ (M : ℝ) * R := by nlinarith
  have hDmem : D ∈ Finset.Icc 1 (2 * R) := Finset.mem_Icc.mpr ⟨hD, by omega⟩
  have hb : ‖quadraticGcdMomentError M R K D J v‖ ≤
      (C * (((M : ℝ) * R) ^ 4 / J ^ A)) * (2 * R) * quadraticSieveEnergy (2 * R) v := by
    unfold quadraticGcdMomentError
    have hcast : (2 * (R : ℝ)) = ((2 * R : ℕ) : ℝ) := by push_cast; rfl
    rw [hcast]
    apply quadratic_gcd_pair_support_bound hDmem v _ (by dsimp [C]; positivity)
    intro z hz hv hw
    have hne := quadratic_small_gcd_ne_diagonal hDR v hsupp hz hv
    obtain ⟨hz', _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
    have hlo : R ≤ z.1 := by by_contra! hh; exact hv (hsupp _ hs hh)
    have hhi : R ≤ z.2 := by by_contra! hh; exact hw (hsupp _ ht hh)
    obtain ⟨hqlo, hqhi⟩ := quadratic_pair_dyadic_kernel hz hlo hhi
    have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2
    have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
    have hqne : quadraticPairKernel z.1 z.2 ≠ 1 :=
      mt (quadraticPairKernel_eq_one_iff (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).mp hne
    have he₁ := hc₁ M (2 * R) D K (by omega) J hJ
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcut) z hz hne
    have he₂ := hc₂ M D _ K (by omega) hsf ho hqne ((R : ℝ) / D) J
      (by positivity) hJ hqlo hqhi
    have he₃ := hc₃ M K D _ (by omega) hD (Nat.pos_of_ne_zero hsf.ne_zero) J hJ
    have hcost₁ : 4 * C₁ * ((2 * R : ℕ) : ℝ) ^ 4 / ((M : ℝ) * J ^ A) ≤
        64 * C₁ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hrpow := pow_le_pow_left₀ (Nat.cast_nonneg R) hRprod 4
      have hmdiv : (R : ℝ) ^ 4 / M ≤ ((M : ℝ) * R) ^ 4 :=
        (div_le_self (by positivity) hMR).trans hrpow
      calc
        _ = 64 * C₁ * ((R : ℝ) ^ 4 / M) / J ^ A := by push_cast; ring
        _ ≤ 64 * C₁ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmdiv (by positivity)) (by positivity)
        _ = _ := by ring
    have hcost₂ : C₂ * Real.sqrt M * D * K / J ^ A ≤
        C₂ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hh : Real.sqrt M * D * K ≤ ((M : ℝ) * R) ^ 4 := by
        calc
          _ ≤ (M : ℝ) * R * (((M : ℝ) * R) ^ 3) := by
            gcongr
            exact Real.sqrt_le_self_iff.mpr (Or.inr hMR)
          _ = _ := by ring
      calc
        _ = C₂ * (Real.sqrt M * D * K) / J ^ A := by ring
        _ ≤ C₂ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC₂.le) (by positivity)
        _ = _ := by ring
    have hcost₃ : C₃ * Real.sqrt M * K / J ^ A ≤
        C₃ * (((M : ℝ) * R) ^ 4 / J ^ A) := by
      have hh : Real.sqrt M * K ≤ ((M : ℝ) * R) ^ 4 := by
        calc
          _ ≤ ((M : ℝ) * R) * (((M : ℝ) * R) ^ 3) := by
            gcongr
            exact (Real.sqrt_le_self_iff.mpr (Or.inr hMR)).trans hMprod
          _ = _ := by ring
      calc
        _ = C₃ * (Real.sqrt M * K) / J ^ A := by ring
        _ ≤ C₃ * (((M : ℝ) * R) ^ 4) / J ^ A :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC₃.le) (by positivity)
        _ = _ := by ring
    apply ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    dsimp [C]
    linarith
  apply hb.trans
  have hp : ((M : ℝ) * R) ^ 5 ≤ ((M : ℝ) * R) ^ 6 := pow_le_pow_right₀ hprod (by omega)
  have hn : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply mul_le_mul_of_nonneg_right _ hn
  calc
    _ ≤ (2 * C) * (((M : ℝ) * R) ^ 5 / J ^ A) := by
      have hc : 0 ≤ C := by dsimp [C]; positivity
      have hh := mul_le_mul_of_nonneg_left hRprod (show 0 ≤ 2 * C * (((M : ℝ) * R) ^ 4 / J ^ A) by positivity)
      convert hh using 1 <;> ring
    _ ≤ _ := by gcongr

end Ostmann

end OAI
