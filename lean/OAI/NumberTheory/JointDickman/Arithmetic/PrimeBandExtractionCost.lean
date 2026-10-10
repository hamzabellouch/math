import OAI.NumberTheory.JointDickman.Analysis.CanonicalMellinBands

namespace OAI

/-! # Summability of all prime-square and width errors in the MRT bands -/
namespace JointDickman
open Finset TwoPointCorrelations

lemma sum_range_succ_eq_Icc (f : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ range J, f (j+1)) = ∑ j ∈ Icc 1 J, f j := by
  apply sum_bij (fun j _ => j+1)
  · intro j hj
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩
  · intro j _ k _ hjk
    omega
  · intro j hj
    refine ⟨j-1, mem_range.mpr (by have := mem_Icc.mp hj; omega), ?_⟩
    have := mem_Icc.mp hj
    omega
  · intro j _
    rfl

lemma sum_range_succ_inv_sq_le (J : ℕ) :
    (∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹) ≤ 2 := by
  rw [sum_range_succ_eq_Icc (fun j => ((j : ℝ)^2)⁻¹) J]
  have he : Icc 1 J = Ioo 0 (J+1) := by ext j; simp; omega
  rw [he]
  simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 (J+1)

lemma primeBand_square_mass_le {L U : ℝ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    (∑ p ∈ mrtPrimeBand L U, 1 / (p : ℝ)^2) ≤ 2/L := by
  have hL0 : 0 < L := by linarith
  have hM : 0 < ⌊L⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hMN : ⌊L⌋₊ ≤ ⌊U⌋₊ := Nat.floor_mono hLU
  have hsub : mrtPrimeBand L U ⊆ Ioc ⌊L⌋₊ ⌊U⌋₊ := by
    intro p hp
    have hh := mrtPrimeBand_bounds hL0.le (hL0.le.trans hLU) hp
    exact mem_Ioc.mpr ⟨(Nat.floor_lt hL0.le).mpr hh.1,
      (Nat.le_floor_iff (hL0.le.trans hLU)).mpr hh.2⟩
  have hs : (∑ p ∈ mrtPrimeBand L U, 1 / (p : ℝ)^2) ≤ (⌊L⌋₊ : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ p ∈ Ioc ⌊L⌋₊ ⌊U⌋₊, 1 / (p : ℝ)^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ (⌊L⌋₊ : ℝ)⁻¹ - (⌊U⌋₊ : ℝ)⁻¹ := by
        simpa only [one_div] using sum_Ioc_inv_sq_le_sub (α := ℝ) hM.ne' hMN
      _ ≤ _ := sub_le_self _ (by positivity)
  apply hs.trans
  rw [← one_div]
  apply (div_le_div_iff₀ (by exact_mod_cast hM) hL0).mpr
  have hh := Nat.lt_floor_add_one L
  nlinarith

lemma mrt_band_lower_ge_square {P Q : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (j : ℕ) (hj : 1 ≤ j) :
    P * (j : ℝ)^2 ≤ mrtBandLower P Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hp : (j : ℝ)^2 ≤ (j : ℝ)^(4*j) :=
    pow_le_pow_right₀ hj1 (by omega)
  have hq : 1 ≤ Real.log Q^(j-1) := one_le_pow₀ hQ
  have hexp : Real.log P + 2*Real.log (j : ℝ) ≤
      (j : ℝ)^(4*j) * Real.log Q^(j-1) * Real.log P := by
    have hjlog := Real.log_le_sub_one_of_pos hj0
    have hm : (j : ℝ)^2 ≤ (j : ℝ)^(4*j) * Real.log Q^(j-1) := by
      nlinarith [pow_nonneg hj0.le (4*j)]
    have hh := mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ Real.log P)
    have hz : 0 ≤ ((j : ℝ)^2-1)*(Real.log P-2) :=
      mul_nonneg (by nlinarith) (by linarith)
    nlinarith [sq_nonneg ((j : ℝ)-1)]
  calc
    _ = Real.exp (Real.log P + 2*Real.log (j : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hP0, show Real.exp (2*Real.log (j : ℝ)) =
        (Real.exp (Real.log (j : ℝ)))^2 by simpa using Real.exp_nat_mul (Real.log (j : ℝ)) 2,
        Real.exp_log hj0]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

lemma canonical_square_mass_le {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q) (j : ℕ) :
    (∑ p ∈ (canonicalMellinBands P Q η).primes j, 1/(p : ℝ)^2) ≤
      (2/P) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
  have he2 : 2 ≤ P := by
    have he := Real.add_one_le_exp (2 : ℝ)
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith
  have hL := mrt_band_lower_ge_square hP0 hP hQ (j+1) (by omega)
  have hl := mrt_band_endpoints P Q (j+1) (by omega) he2 hPQ hQ
  have hsq : (0 : ℝ) < ((j+1 : ℕ) : ℝ)^2 := by positivity
  apply (primeBand_square_mass_le hl.1 hl.2).trans
  calc
    _ ≤ 2/(P*((j+1 : ℕ) : ℝ)^2) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hP0 hsq) hL
    _ = _ := by ring

lemma canonical_square_mass_le_one {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q) (j : ℕ) :
    (∑ p ∈ (canonicalMellinBands P Q η).primes j, 1/(p : ℝ)^2) ≤ 1 := by
  have hh := canonical_square_mass_le (η := η) hP0 hP hQ hPQ j
  have hP2 : 2 ≤ P := by
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hj : (1 : ℝ) ≤ ((j+1 : ℕ) : ℝ)^2 := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ j+1 by omega))
  have h1 : 2/P ≤ 1 := (div_le_one hP0).mpr hP2
  have h2 : (((j+1 : ℕ) : ℝ)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj
  exact hh.trans ((mul_le_mul h1 h2 (by positivity) zero_le_one).trans_eq (one_mul 1))

theorem canonical_extraction_sum_le {P Q η : ℝ} (J N : ℕ) {T : ℝ}
    (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hT : 0 ≤ T) :
    (∑ j ∈ range J, (canonicalMellinBands P Q η).extractionCost j N T) ≤
      2816 * Real.exp 1 * (T/N+1) * (8/P + 4/(mrtBaseResolution P Q η)) := by
  let D := canonicalMellinBands P Q η
  have hterm (j : ℕ) : D.extractionCost j N T ≤
      (2816 * Real.exp 1 * (T/N+1)) *
        ((4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹) := by
    have hm0 : 0 ≤ ∑ p ∈ D.primes j, 1/(p : ℝ)^2 := by positivity
    have hm1 := canonical_square_mass_le_one (η := η) hP0 hP hQ hPQ j
    have hm := canonical_square_mass_le (η := η) hP0 hP hQ hPQ j
    have hw := (mrt_prime_log_width (canonical_resolution_ge_two hH j)).2.2
    change D.resolution j - 1 ≤ 2 / mrtResolution P Q η (j+1) at hw
    have he : 2 / mrtResolution P Q η (j+1) =
        (2 / mrtBaseResolution P Q η) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      unfold mrtResolution
      ring
    rw [he] at hw
    unfold MellinPrimeBands.extractionCost
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change 0 ≤ _ at hm0
    change _ ≤ 1 at hm1
    change _ ≤ _ at hm
    dsimp only [D] at *
    have hec : (4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹ =
        2 * ((2/P) * (((j+1 : ℕ) : ℝ)^2)⁻¹) +
          (2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by ring
    rw [hec]
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]
  calc
    _ ≤ ∑ j ∈ range J, (2816 * Real.exp 1 * (T/N+1)) *
        ((4/P + 2/(mrtBaseResolution P Q η)) * (((j+1 : ℕ) : ℝ)^2)⁻¹) :=
      sum_le_sum (fun j _ => hterm j)
    _ = (2816 * Real.exp 1 * (T/N+1)) * (4/P + 2/(mrtBaseResolution P Q η)) *
        ∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ (2816 * Real.exp 1 * (T/N+1)) * (4/P + 2/(mrtBaseResolution P Q η)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_succ_inv_sq_le J) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
