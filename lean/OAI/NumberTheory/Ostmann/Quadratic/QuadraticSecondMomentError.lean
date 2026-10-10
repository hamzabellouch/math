import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSecondKernel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalError

namespace OAI

/-! # The full second-Poisson remainder on the original dyadic coefficient block -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_remainder_support_bound (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ D ∈ Finset.Icc 1 N, ∀ z ∈ quadraticGcdPairs N D,
      v z.1 ≠ 0 → v z.2 ≠ 0 → ‖E D z‖ ≤ T) :
    ‖quadraticGcdRemainder N v E‖ ≤ T * N * quadraticSieveEnergy N v := by
  let F (D : ℕ) (z : ℕ × ℕ) := if v z.1 = 0 ∨ v z.2 = 0 then 0 else E D z
  have he : quadraticGcdRemainder N v E = quadraticGcdRemainder N v F := by
    unfold quadraticGcdRemainder
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro z _
    dsimp [F]
    by_cases hz : v z.1 = 0 ∨ v z.2 = 0
    · rw [ite_eq_left hz]
      rcases hz with h | h <;> simp [h]
    · rw [ite_eq_right hz]
  rw [he]
  apply quadratic_gcd_remainder_bound N v F hT
  intro D hD z hz
  dsimp [F]
  split_ifs with h
  · simpa only [norm_zero] using hT
  · exact hE D hD z hz (fun hh => h (Or.inl hh)) (fun hh => h (Or.inr hh))

theorem quadratic_pair_dyadic_kernel {R D : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ quadraticGcdPairs (2 * R) D) (h₁ : R ≤ z.1) (h₂ : R ≤ z.2) :
    ((R : ℝ) / D) ^ 2 ≤ quadraticPairKernel z.1 z.2 ∧
      (quadraticPairKernel z.1 z.2 : ℝ) ≤ 4 * ((R : ℝ) / D) ^ 2 := by
  obtain ⟨hD, _, _⟩ := quadratic_pair_product_bound hz
  obtain ⟨hz', hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
  have hs' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have ht' := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  have hp : (D : ℝ) ^ 2 * quadraticPairKernel z.1 z.2 = (z.1 : ℝ) * z.2 := by
    have hh := quadraticPairKernel_factor z.1 z.2
    rw [hg] at hh
    exact_mod_cast hh
  have hlo : (R : ℝ) ^ 2 ≤ (z.1 : ℝ) * z.2 := by
    have hh := Nat.mul_le_mul h₁ h₂
    have hhR : (R : ℝ) * R ≤ (z.1 : ℝ) * z.2 := by exact_mod_cast hh
    nlinarith
  have hhi : (z.1 : ℝ) * z.2 ≤ 4 * (R : ℝ) ^ 2 := by
    have hh := Nat.mul_le_mul hs' ht'
    have hh' : (z.1 : ℝ) * z.2 ≤ (2 * (R : ℝ)) * (2 * R) := by exact_mod_cast hh
    nlinarith
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · rw [div_pow]
    apply (div_le_iff₀ (pow_pos hDR 2)).mpr
    nlinarith
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hDR 2)).mpr
    nlinarith

noncomputable def quadraticSecondMomentError (M R K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  quadraticGcdRemainder (2 * R) v (fun D z => if z.1 = z.2 then 0 else
    quadraticFirstKernelFinite M D (quadraticPairKernel z.1 z.2) K -
      quadraticFirstSecondKernel M D (quadraticPairKernel z.1 z.2) K ((R : ℝ) / D) J)

theorem quadratic_second_moment_error (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K : ℕ, 0 < M → 0 < R → ∀ J : ℝ, 1 ≤ J →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticSecondMomentError M R K J v‖ ≤
        C * Real.sqrt M * (R : ℝ) ^ 2 * K / J ^ A * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_first_second_kernel_error A
  refine ⟨4 * C, by positivity, ?_⟩
  intro M R K hM hR J hJ v hsupp
  have hh : ‖quadraticSecondMomentError M R K J v‖ ≤
      (C * Real.sqrt M * (2 * R) * K / J ^ A) * (2 * R) * quadraticSieveEnergy (2 * R) v := by
    unfold quadraticSecondMomentError
    have hcast : ((2 * R : ℕ) : ℝ) = 2 * R := by push_cast; rfl
    rw [← hcast]
    apply quadratic_gcd_remainder_support_bound (2 * R) v _ (by positivity)
    intro D hD z hz hv₁ hv₂
    by_cases heq : z.1 = z.2
    · rw [ite_eq_left heq, norm_zero]
      positivity
    · rw [ite_eq_right heq]
      obtain ⟨hz', _⟩ := Finset.mem_filter.mp hz
      obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz'
      have hslo : R ≤ z.1 := by
        by_contra! hn
        exact hv₁ (hsupp z.1 hs hn)
      have htlo : R ≤ z.2 := by
        by_contra! hn
        exact hv₂ (hsupp z.2 ht hn)
      obtain ⟨hqlo, hqhi⟩ := quadratic_pair_dyadic_kernel hz hslo htlo
      have hDpos : 0 < D := (Finset.mem_Icc.mp hD).1
      have hDN : (D : ℝ) ≤ 2 * R := by exact_mod_cast (Finset.mem_Icc.mp hD).2
      have hsf := quadraticPairKernel_squarefree (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2
      have ho := quadraticPairKernel_odd (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp ht).2.1
      have hq : quadraticPairKernel z.1 z.2 ≠ 1 :=
        mt (quadraticPairKernel_eq_one_iff (Finset.mem_filter.mp hs).2.2 (Finset.mem_filter.mp ht).2.2).mp heq
      apply (hc M D _ K hM hsf ho hq ((R : ℝ) / D) J (by positivity) hJ hqlo hqhi).trans
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      gcongr
  convert hh using 1
  ring

theorem quadratic_polynomial_error_power_choice {δ : ℝ} (hδ : 0 < δ) (P Q : ℕ) :
    ∃ A : ℕ, ∀ X : ℝ, 1 ≤ X → X ^ Q / (X ^ δ) ^ A ≤ 1 / X ^ P := by
  obtain ⟨A, hA⟩ := exists_nat_ge (((P : ℝ) + Q) / δ)
  refine ⟨A, ?_⟩
  intro X hX
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hexp : (P : ℝ) + Q ≤ δ * A := by
    have hh := (div_le_iff₀ hδ).mp hA
    nlinarith
  have hp : X ^ (P + Q) ≤ (X ^ δ) ^ A := by
    calc
      _ = X ^ ((P : ℝ) + Q) := by rw [← Real.rpow_natCast, Nat.cast_add]
      _ ≤ X ^ (δ * A) := Real.rpow_le_rpow_of_exponent_le hX hexp
      _ = _ := by rw [Real.rpow_mul hX₀.le, Real.rpow_natCast]
  calc
    _ ≤ X ^ Q / X ^ (P + Q) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hX₀ _) hp
    _ = _ := by rw [pow_add]; field_simp

theorem quadratic_second_moment_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K : ℕ, 1 ≤ M → 1 ≤ R →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 → ∀ J : ℝ, ((M : ℝ) * R) ^ δ ≤ J → ∀ v : ℕ → ℂ,
      (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticSecondMomentError M R K J v‖ ≤
        C / (((M : ℝ) * R) ^ P) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A, hA⟩ := quadratic_polynomial_error_power_choice hδ P 6
  obtain ⟨C, hC, hc⟩ := quadratic_second_moment_error A
  refine ⟨C, hC, ?_⟩
  intro M R K hM hR hK J hJlower v hsupp
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRR : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hMRR : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le hMR hRR
  have hJbase : 1 ≤ ((M : ℝ) * R) ^ δ := Real.one_le_rpow hMRR hδ.le
  have hJ : 1 ≤ J := hJbase.trans hJlower
  have hcost : Real.sqrt M * (R : ℝ) ^ 2 * K ≤ ((M : ℝ) * R) ^ 6 := by
    calc
      _ ≤ (M : ℝ) ^ 2 * (R : ℝ) ^ 2 * (((M : ℝ) * R) ^ 3) := by
        gcongr
        exact (Real.sqrt_le_self_iff.mpr (Or.inr hMR)).trans (by nlinarith)
      _ = ((M : ℝ) * R) ^ 5 := by ring
      _ ≤ _ := pow_le_pow_right₀ hMRR (by omega)
  have hp := hA ((M : ℝ) * R) hMRR
  have hEn : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ C * Real.sqrt M * (R : ℝ) ^ 2 * K / J ^ A *
        quadraticSieveEnergy (2 * R) v := hc M R K (by omega) (by omega) J hJ v hsupp
    _ ≤ C * Real.sqrt M * (R : ℝ) ^ 2 * K / (((M : ℝ) * R) ^ δ) ^ A *
        quadraticSieveEnergy (2 * R) v := by gcongr
    _ = C * (Real.sqrt M * (R : ℝ) ^ 2 * K / (((M : ℝ) * R) ^ δ) ^ A) *
        quadraticSieveEnergy (2 * R) v := by ring
    _ ≤ C * (((M : ℝ) * R) ^ 6 / (((M : ℝ) * R) ^ δ) ^ A) * quadraticSieveEnergy (2 * R) v := by gcongr
    _ ≤ C * (1 / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v := by gcongr
    _ = _ := by ring

end Ostmann

end OAI
