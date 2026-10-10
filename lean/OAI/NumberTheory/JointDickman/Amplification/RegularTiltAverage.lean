import OAI.NumberTheory.JointDickman.Amplification.WeightedEndpointPair

namespace OAI

/-! # Tilted remainder averages with the regularity event retained -/

namespace JointDickman
open Finset Classical

noncomputable def regularTiltAverage (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (F : Finset ℕ → ℝ) : ℝ :=
  ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
      if RegularPrimeSet B L τ C U then F U else 0

theorem remainderTiltMass_nonneg (B : ℕ) (A U : Finset ℕ)
    (hU : U ∈ (auxiliaryPrimes B \ A).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp hU)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  exact ⟨div_nonneg (by norm_num) (by linarith), (div_le_one (by linarith : (0 : ℝ) < 2*p-1)).mpr (by linarith)⟩

theorem regularTiltAverage_mono {B L : ℕ} {τ C : ℝ} {A : Finset ℕ}
    {F G : Finset ℕ → ℝ}
    (h : ∀ U ∈ (auxiliaryPrimes B \ A).powerset,
      RegularPrimeSet B L τ C U → F U ≤ G U) :
    regularTiltAverage B L τ C A F ≤ regularTiltAverage B L τ C A G := by
  apply sum_le_sum
  intro U hU
  apply mul_le_mul_of_nonneg_left _ (remainderTiltMass_nonneg B A U hU)
  split_ifs with hr
  · exact h U hU hr
  · rfl

theorem regularTiltAverage_nonneg {B L : ℕ} {τ C : ℝ} {A : Finset ℕ}
    {F : Finset ℕ → ℝ}
    (h : ∀ U ∈ (auxiliaryPrimes B \ A).powerset,
      RegularPrimeSet B L τ C U → 0 ≤ F U) :
    0 ≤ regularTiltAverage B L τ C A F := by
  apply sum_nonneg
  intro U hU
  apply mul_nonneg (remainderTiltMass_nonneg B A U hU)
  split_ifs with hr
  · exact h U hU hr
  · rfl

theorem regularTiltAverage_bound {B L : ℕ} {τ C K : ℝ} {A : Finset ℕ}
    (hK : 0 ≤ K) {F : Finset ℕ → ℝ}
    (h : ∀ U ∈ (auxiliaryPrimes B \ A).powerset,
      RegularPrimeSet B L τ C U → F U ≤ K) :
    regularTiltAverage B L τ C A F ≤ K := by
  calc
    _ ≤ ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U*K := by
      apply sum_le_sum
      intro U hU
      apply mul_le_mul_of_nonneg_left _ (remainderTiltMass_nonneg B A U hU)
      split_ifs with hr
      · exact h U hU hr
      · exact hK
    _ = K := by rw [← sum_mul,bernoulliSubsetMass_sum,one_mul]

theorem regularTiltAverage_add (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (F G : Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => F U+G U) =
      regularTiltAverage B L τ C A F+regularTiltAverage B L τ C A G := by
  unfold regularTiltAverage
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro U _
  split_ifs <;> ring

theorem regularTiltAverage_sum {ι : Type*} (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (s : Finset ι) (F : ι → Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => ∑ i ∈ s, F i U) =
      ∑ i ∈ s, regularTiltAverage B L τ C A (F i) := by
  unfold regularTiltAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  rw [← mul_sum]
  congr 1
  split_ifs <;> simp_all

theorem regularTiltAverage_comm (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (F U)) =
      regularTiltAverage B L τ C D (fun V => regularTiltAverage B L τ C A (fun U => F U V)) := by
  unfold regularTiltAverage
  have he (A D : Finset ℕ) (F : Finset ℕ → Finset ℕ → ℝ) :
      (∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
          if RegularPrimeSet B L τ C U then
            ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V *
                if RegularPrimeSet B L τ C V then F U V else 0
          else 0) =
      ∑ U ∈ (auxiliaryPrimes B \ A).powerset, ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
        bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V *
          if RegularPrimeSet B L τ C U ∧ RegularPrimeSet B L τ C V then F U V else 0 := by
    apply sum_congr rfl
    intro U _
    by_cases hU : RegularPrimeSet B L τ C U
    · simp only [hU,ite_true,true_and,mul_sum]
      apply sum_congr rfl
      intro V _
      ring
    · simp [hU]
  rw [he,he,sum_comm]
  apply sum_congr rfl
  intro V _
  apply sum_congr rfl
  intro U _
  simp only [and_comm]
  ring

end JointDickman

end OAI
