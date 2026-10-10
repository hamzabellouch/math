import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SquarefreeHarmonic

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights

noncomputable def reciprocal : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ)⁻¹, by simp⟩

@[simp] theorem reciprocal_apply (n : ℕ) : reciprocal n = (n : ℝ)⁻¹ := rfl

theorem reciprocal_mult : reciprocal.IsMultiplicative := by
  constructor
  · simp
  · intro m n _
    simp [Nat.cast_mul, mul_inv_rev, mul_comm]

noncomputable def reciprocalSieve (P : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := ∅
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := reciprocal
  nu_mult := reciprocal_mult
  nu_pos_of_prime := by
    intro p hp _
    simp only [reciprocal_apply]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    simp only [reciprocal_apply]
    exact (inv_lt_one₀ (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt)

noncomputable def actualWeights (P z : ℕ) (hP : Squarefree P) : ℕ → ℝ :=
  weights (reciprocalSieve P hP) z

noncomputable def actualMass (P z : ℕ) (hP : Squarefree P) : ℝ :=
  mass (reciprocalSieve P hP) z

lemma actualWeights_one {P z : ℕ} (hP : Squarefree P) (hz : 1 ≤ z) :
    actualWeights P z hP 1 = 1 := weights_one _ hz

lemma actualWeights_abs_le {P z d : ℕ} (hP : Squarefree P) (hz : 1 ≤ z)
    (hd : d ∣ P) : |actualWeights P z hP d| ≤ d := by
  simpa only [actualWeights, reciprocalSieve, reciprocal_apply, inv_inv] using
    weights_abs_le (reciprocalSieve P hP) hz hd

lemma actualWeights_zero_above {P z d : ℕ} (hP : Squarefree P) (hzd : z < d)
    (hd : d ∣ P) : actualWeights P z hP d = 0 :=
  weights_zero_above _ hd hzd

lemma actualMass_log_bound {P z : ℕ} (hP : Squarefree P)
    (hpr : ∀ p, Nat.Prime p → p ≤ z → p ∣ P) :
    Real.log (z+1 : ℕ) ≤ 2 * actualMass P z hP :=
  log_le_twice_mass (reciprocalSieve P hP) z hpr (fun _ _ => le_rfl)

theorem actualWeights_diagonal {P z : ℕ} (hP : Squarefree P) (hz : 1 ≤ z) :
    (∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
      actualWeights P z hP d * actualWeights P z hP e / (Nat.lcm d e : ℝ)) =
        (actualMass P z hP)⁻¹ := by
  let s := reciprocalSieve P hP
  have he := weights_mainSum s hz
  rw [s.mainSum_lambdaSquared_eq_sum_sum_mul] at he
  change _ = (mass s z)⁻¹
  rw [← he]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hg : s.nu (Nat.gcd d e) ≠ 0 := s.nu_ne_zero
    ((Nat.gcd_dvd_left d e).trans (Nat.dvd_of_mem_divisors hd))
  have hl := s.nu_mult.map_lcm hg
  dsimp only [s, reciprocalSieve] at hl
  simpa only [actualWeights, s, reciprocalSieve, div_eq_mul_inv, reciprocal_apply, mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun x => actualWeights P z hP d * actualWeights P z hP e * x) hl

theorem actualWeights_l1 {P z : ℕ} (hP : Squarefree P) (hz : 1 ≤ z) :
    (∑ d ∈ P.divisors, |actualWeights P z hP d|) ≤ (z : ℝ)^2 := by
  have htrunc : (∑ d ∈ P.divisors, |actualWeights P z hP d|) =
      ∑ d ∈ P.divisors.filter (· ≤ z), |actualWeights P z hP d| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hzd : z < d := by simpa only [Finset.mem_filter, hd, true_and, not_le] using hnot
    simp only [actualWeights_zero_above hP hzd (Nat.dvd_of_mem_divisors hd), abs_zero]
  rw [htrunc]
  calc
    _ ≤ ∑ d ∈ P.divisors.filter (· ≤ z), (z : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdP, hdz⟩ := Finset.mem_filter.mp hd
      exact (actualWeights_abs_le hP hz (Nat.dvd_of_mem_divisors hdP)).trans (by exact_mod_cast hdz)
    _ ≤ ∑ d ∈ Finset.Icc 1 z, (z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => Nat.cast_nonneg _)
      intro d hd
      obtain ⟨hdP, hdz⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩
    _ = _ := by simp; ring

noncomputable def sieveWeight (P z : ℕ) (hP : Squarefree P) (n : ℕ) : ℝ :=
  (∑ d ∈ P.divisors, if d ∣ n then actualWeights P z hP d else 0)^2

lemma sieveWeight_nonneg {P z n : ℕ} (hP : Squarefree P) :
    0 ≤ sieveWeight P z hP n := sq_nonneg _

lemma sieveWeight_eq_one_of_coprime {P z n : ℕ} (hP : Squarefree P) (hz : 1 ≤ z)
    (hn : Nat.Coprime n P) : sieveWeight P z hP n = 1 := by
  unfold sieveWeight
  have he : (∑ d ∈ P.divisors, if d ∣ n then actualWeights P z hP d else 0) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp only [one_dvd, ite_true, actualWeights_one hP hz]
    · intro d hd hd1
      have hdn : ¬d ∣ n := by
        intro hdn
        have := Nat.dvd_gcd hdn (Nat.dvd_of_mem_divisors hd)
        rw [hn.gcd_eq_one, Nat.dvd_one] at this
        exact hd1 this
      simp only [ite_eq_right hdn]
    · intro hnot
      exact False.elim (hnot (Nat.mem_divisors.mpr ⟨one_dvd P, hP.ne_zero⟩))
  rw [he, one_pow]

lemma rough_indicator_le {P z n : ℕ} (hP : Squarefree P) (hz : 1 ≤ z) :
    (if Nat.Coprime n P then (1 : ℝ) else 0) ≤ sieveWeight P z hP n := by
  split_ifs with hn
  · rw [sieveWeight_eq_one_of_coprime hP hz hn]
  · exact sieveWeight_nonneg hP

theorem sieveWeight_expansion {P z n : ℕ} (hP : Squarefree P) :
    sieveWeight P z hP n = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
      if Nat.lcm d e ∣ n then actualWeights P z hP d * actualWeights P z hP e else 0 := by
  simp only [sieveWeight, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  simp only [Nat.lcm_dvd_iff]
  split_ifs <;> simp_all

end OrdinarySelbergWeights

end

end OAI
