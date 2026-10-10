import OAI.NumberTheory.Ostmann.QuadraticSieveLargeGcdBound

namespace OAI

namespace Ostmann.QuadraticSieve

theorem weightedNumeratorEnergy_le_gcdMass (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ)
    (N : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    weightedNumeratorEnergy W S ω a ≤ ∑ d ∈ Finset.Icc 1 N, weightedGcdMass W S ω a d := by
  calc
    _ ≤ ∑ m ∈ W, ω m * ∑ d ∈ Finset.Icc 1 N, ‖gcdJacobiRow S a d m‖ :=
      Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left
        (norm_sum_sq_le_sum_norm_gcdCorrelation S
          (fun n => a n * (jacobiSym m n : ℂ)) N hS) (hω m hm))
    _ = _ := by
      simp only [Finset.mul_sum, weightedGcdMass]
      rw [Finset.sum_comm]

noncomputable def weightedGcdCorrelation (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ m ∈ W, (ω m : ℂ) * gcdJacobiRow S a d m

theorem weightedNumeratorEnergy_eq_gcdCorrelation (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (a : ℕ → ℂ) (N : ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (weightedNumeratorEnergy W S ω a : ℂ) =
      ∑ d ∈ Finset.Icc 1 N, weightedGcdCorrelation W S ω a d := by
  unfold weightedGcdCorrelation
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, gcdJacobiRow, sum_gcdCorrelation S _ N hS]
  unfold weightedNumeratorEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  exact (Complex.mul_conj' _).symm

theorem norm_weightedGcdCorrelation_le_mass (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ) (d : ℕ) :
    ‖weightedGcdCorrelation W S ω a d‖ ≤ weightedGcdMass W S ω a d := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hω m hm), le_refl]

theorem weightedNumeratorEnergy_le_gcdCorrelation (W : Finset ℤ) (S : Finset ℕ)
    (ω : ℤ → ℝ) (hω : ∀ m ∈ W, 0 ≤ ω m) (a : ℕ → ℂ)
    (N : ℕ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    weightedNumeratorEnergy W S ω a ≤
      ∑ d ∈ Finset.Icc 1 N, ‖weightedGcdCorrelation W S ω a d‖ := by
  have he := congrArg norm (weightedNumeratorEnergy_eq_gcdCorrelation W S ω a N hS)
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weightedNumeratorEnergy_nonneg W S ω hω a)] at he
  rw [he]
  exact norm_sum_le _ _

theorem weighted_large_gcd_removal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Finset ℤ) (S : Finset ℕ)
      (ω : ℤ → ℝ) (a : ℕ → ℂ) (N D : ℕ),
      (∀ m ∈ W, 0 ≤ ω m) → S ⊆ oddSquarefreeUpTo N → 0 < D →
      weightedNumeratorEnergy W S ω a ≤
        (∑ d ∈ Finset.Icc 1 D, ‖weightedGcdCorrelation W S ω a d‖) +
        C * (N : ℝ) ^ ε * weightedNumeratorNorm W (oddSquarefreeUpTo (N / D)) ω *
          coefficientEnergy S a := by
  obtain ⟨C, hC, hlarge⟩ := sum_weightedGcdMass_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro W S ω a N D hω hS hD
  have hSN : ∀ n ∈ S, 0 < n ∧ n ≤ N := fun n hn =>
    ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1, (mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩
  apply (weightedNumeratorEnergy_le_gcdCorrelation W S ω hω a N hSN).trans
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun d => d ≤ D)]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdN, hdD⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdN).1, hdD⟩
    · intro d hd hnot
      exact norm_nonneg _
  · apply (Finset.sum_le_sum (fun d hd =>
      norm_weightedGcdCorrelation_le_mass W S ω hω a d)).trans
    apply hlarge W _ S ω a N D hω hS hD
    intro d hd
    exact (Nat.lt_of_not_ge (Finset.mem_filter.mp hd).2).le

end Ostmann.QuadraticSieve

end OAI
