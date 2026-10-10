import OAI.NumberTheory.DirichletL.CubicSieve.QuotientColumns
import OAI.NumberTheory.DirichletL.CubicSieve.Recurrence

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def frequencyCost (C ε : ℝ) (hε : 0 < ε) (M N : ℝ) : ℝ :=
  M * (2/N) * (‖paperRadialFourier rowMajorant 0‖ +
    C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
      ∑' l : ℕ, frequencyMajorant M N l)

theorem cubic_common_factor_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M)
        (cols : n → Ideal O) (_hinj : Function.Injective cols)
        (_hc : ∀ j, Admissible (cols j))
        (_hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ) (R : Finset O)
        (_hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M),
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
          ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
            frequencyCost C ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ)) *
              ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
  obtain ⟨C,hC,hrec⟩ := cubic_smoothed_frequency_recurrence_all rowMajorant
  refine ⟨C,hC,?_⟩
  intro n _ _ ε hε M N hM cols hinj hc hcols a R hR
  apply (finite_energy_le_compact_descendants cols hc a R M hM hR).trans
  apply Finset.sum_le_sum
  intro D hD
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  have hDcol := gcdPool_subset_columnDivisorPool cols hc0 hD
  have hDN := columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D hDcol
  have hD0 := gcdPool_ne_zero cols hc0 D hD
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith [hDN.1]
  have hNshort : 1 ≤ N / (Ideal.absNorm D : ℝ) := (one_le_div hDN0).mpr hDN.2
  apply Finset.sum_le_sum
  intro E hE
  have hEdiv := (mem_idealDivisors hD0).mp hE
  have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hEdiv
  have hEN : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  rw [compact_descendant_restrict]
  have hh := hrec ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ))
    (div_pos hM hEN) hNshort (quotientColumn D cols) (quotientColumn_injective D cols hinj)
    (fun j => ⟨quotientColumn_admissible D cols hc j, cubic_quotient_in_shell D cols hc N hcols j⟩)
    (quotientCoefficient D cols a (idealGenerator E))
  rw [quotientCoefficient_energy] at hh
  convert hh using 1
  dsimp only [frequencyCost]
  ring

theorem common_factor_uniform_cost {n : Type*} [Fintype n]
    (C ε U M N : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hnorm : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ)
    (hcost : ∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U) :
    (∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) *
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
      U*(DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2 := by
  have he := descended_energy_small_power ε hε cols hc N hN hnorm a
  have hsub := gcdPool_subset_columnDivisorPool cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hc j).2)
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        U * ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcost D hD E hE) (by positivity)
    _ = U*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      simp only [Finset.mul_sum]
    _ ≤ U*(∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hU
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hnot => by positivity)
    _ ≤ U*((DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left he hU
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
