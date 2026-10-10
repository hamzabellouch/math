import OAI.NumberTheory.Ostmann.Quadratic.KernelResidueCount
import OAI.NumberTheory.Ostmann.Arithmetic.ResiduePopulationCount
import OAI.NumberTheory.Ostmann.Arithmetic.UnitResidueGrowth

namespace OAI

/-! # The congruence-refined population bound for a fixed signed kernel -/

namespace Ostmann

open scoped Classical

theorem kernel_population_residue_bound (S : Finset ℤ) (root : ℤ → ℕ)
    (m D : ℕ) (hm : 0 < m) (h u : ℤ) (hu : u ≠ 0) (hred : h.natAbs.Coprime m)
    (X : ℝ) (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hD : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ D) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (m.primeFactors.card + 1) * ((D : ℝ) / m + 2) := by
  let : NeZero m := ⟨hm.ne'⟩
  have hcount := nat_residue_population_card_le (kernelRootPopulation S root) m D hm
    (kernelRootPopulation_diameter S root m D h u hu X hroot hspan hD)
  have hres : (((kernelRootPopulation S root).image (fun t : ℕ => (t : ZMod m))).card : ℝ) ≤
      (2 : ℝ) ^ (m.primeFactors.card + 1) := by
    exact_mod_cast kernel_root_residues_card_le S root m h u hred hroot
  rw [kernelRootPopulation_card S root m hm h u hroot] at hcount
  exact hcount.trans (mul_le_mul_of_nonneg_right hres (by positivity))

theorem kernel_population_real_bound (S : Finset ℤ) (root : ℤ → ℕ)
    (m : ℕ) (hm : 0 < m) (h u : ℤ) (hu : u ≠ 0) (hred : h.natAbs.Coprime m)
    (X : ℝ) (hroot : ∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hspan : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) :
    (S.card : ℝ) ≤ (2 : ℝ) ^ (m.primeFactors.card + 1) *
      (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3) := by
  let R := Real.sqrt ((m : ℝ) * X / |(u : ℝ)|)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hb := kernel_population_residue_bound S root m ⌈R⌉₊ hm h u hu hred X hroot hspan
    (Nat.le_ceil R)
  have hceil : (⌈R⌉₊ : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one hR).le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdiv : (⌈R⌉₊ : ℝ) / m + 2 ≤ R / m + 3 := by
    have he := div_le_div_of_nonneg_right hceil (Nat.cast_nonneg m)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hunit : (1 : ℝ) / m ≤ 1 := (div_le_one hm0).mpr hm1
    rw [add_div] at he
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hdiv (by positivity))

private theorem sqrt_modulus_cancel (m X v : ℝ) (hm : 0 < m) :
    Real.sqrt m * (Real.sqrt (m * X / v) / m) = Real.sqrt (X / v) := by
  have heq : m * X / v = m * (X / v) := by ring
  rw [heq, Real.sqrt_mul hm.le]
  calc
    _ = (Real.sqrt m ^ 2 / m) * Real.sqrt (X / v) := by ring
    _ = _ := by rw [Real.sq_sqrt hm.le, div_self hm.ne', one_mul]

/-- The denominator loss is absorbed into an absolute constant. The remaining
sqrt(m) term is subpower for the common centers constructed in the application. -/
theorem exists_kernel_population_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℤ) (root : ℤ → ℕ) (m : ℕ) (h u : ℤ) (X : ℝ),
      0 < m → u ≠ 0 → h.natAbs.Coprime m →
      (∀ x ∈ S, u * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (S.card : ℝ) ≤ C * (Real.sqrt (X / |(u : ℝ)|) + Real.sqrt m) := by
  obtain ⟨C, hC, hgrowth⟩ := exists_unit_residue_sqrt_bound
  refine ⟨3 * C, by positivity, ?_⟩
  intro S root m h u X hm hu hred hroot hspan
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := kernel_population_real_bound S root m hm h u hu hred X hroot hspan
  have hg := hgrowth m hm.ne'
  have hn : 0 ≤ Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3 := by positivity
  apply hb.trans
  calc
    _ ≤ (C * Real.sqrt m) * (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 3) :=
      mul_le_mul_of_nonneg_right hg hn
    _ = C * (Real.sqrt (X / |(u : ℝ)|) + 3 * Real.sqrt m) := by
      rw [mul_add]
      have hs := sqrt_modulus_cancel (m : ℝ) X |(u : ℝ)| hmR
      calc
        _ = C * (Real.sqrt m * (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m)) +
            3 * C * Real.sqrt m := by ring
        _ = _ := by rw [hs]; ring
    _ ≤ _ := by nlinarith [Real.sqrt_nonneg (X / |(u : ℝ)|)]

end Ostmann

end OAI
