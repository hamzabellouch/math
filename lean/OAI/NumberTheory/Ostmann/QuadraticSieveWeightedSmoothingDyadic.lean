import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedSmoothing

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def dyadicSquarefreeRows (M : ℕ) : Finset ℕ :=
  (oddSquarefreeUpTo (2 * M)).filter (fun v => M < v)

@[simp] theorem mem_dyadicSquarefreeRows {M v : ℕ} :
    v ∈ dyadicSquarefreeRows M ↔ M < v ∧ v ≤ 2 * M ∧ Odd v ∧ Squarefree v := by
  simp only [dyadicSquarefreeRows, Finset.mem_filter, mem_oddSquarefreeUpTo]
  constructor
  · rintro ⟨⟨hv1, hv2, hvo, hvs⟩, hvM⟩
    exact ⟨hvM, hv2, hvo, hvs⟩
  · rintro ⟨hvM, hv2, hvo, hvs⟩
    exact ⟨⟨by omega, hv2, hvo, hvs⟩, hvM⟩

theorem squarefreeKernel_of_squarefree {v : ℕ} (hv : Squarefree v) : squarefreeKernel v = v := by
  simpa only [one_pow, one_mul] using squarefreeKernel_sq_mul (u := 1) (by norm_num) hv

theorem dyadicRow_mem_smoothingRows {M K v : ℕ} (hK : K ≤ M)
    (hv : v ∈ dyadicSquarefreeRows M) : (v : ℤ) ∈ smoothingRows M K := by
  obtain ⟨hvM, hv2M, hvo, hvs⟩ := mem_dyadicSquarefreeRows.mp hv
  apply mem_smoothingRows.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show 1 ≤ v by omega)
  · exact_mod_cast (show v ≤ 3 * M by omega)
  · exact_mod_cast hvo
  · simpa only [Int.natAbs_natCast, squarefreeKernel_of_squarefree hvs] using hK.trans_lt hvM

theorem smoothingWeight_one_dyadic {M v : ℕ} (hM : 0 < M)
    (hv : v ∈ dyadicSquarefreeRows M) : smoothingWeight M (v : ℤ) = 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨hvM, hv2M, hvo, hvs⟩ := mem_dyadicSquarefreeRows.mp hv
  unfold smoothingWeight
  simp only [Int.cast_natCast]
  apply sieveBump_one
  constructor
  · apply (le_div_iff₀ hMr).mpr
    simpa only [one_mul] using (show (M : ℝ) ≤ v by exact_mod_cast hvM.le)
  · apply (div_le_iff₀ hMr).mpr
    exact_mod_cast hv2M

theorem numeratorEnergy_dyadic_le_smoothingEnergy {M K : ℕ} (hM : 0 < M) (hK : K ≤ M)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    numeratorEnergy 1 (dyadicSquarefreeRows M) S a ≤ smoothingEnergy M K S a := by
  classical
  have hsub : (dyadicSquarefreeRows M).image (fun v : ℕ => (v : ℤ)) ⊆ smoothingRows M K := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    exact dyadicRow_mem_smoothingRows hK hv
  have heq : numeratorEnergy 1 (dyadicSquarefreeRows M) S a =
      ∑ m ∈ (dyadicSquarefreeRows M).image (fun v : ℕ => (v : ℤ)),
        smoothingWeight M m * ‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 := by
    rw [Finset.sum_image (fun v hv t ht h => Int.ofNat_inj.mp h)]
    unfold numeratorEnergy
    apply Finset.sum_congr rfl
    intro v hv
    rw [smoothingWeight_one_dyadic hM hv]
    simp only [one_mul]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun m hm hnot => mul_nonneg (smoothingWeight_nonneg M m) (sq_nonneg _))

theorem numeratorEnergy_dyadic_le_smoothingNorm {M K : ℕ} (hM : 0 < M) (hK : K ≤ M)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    numeratorEnergy 1 (dyadicSquarefreeRows M) S a ≤ smoothingNorm M K S * coefficientEnergy S a :=
  (numeratorEnergy_dyadic_le_smoothingEnergy hM hK S a).trans (smoothingEnergy_le_norm M K S a)

end Ostmann.QuadraticSieve

end OAI
