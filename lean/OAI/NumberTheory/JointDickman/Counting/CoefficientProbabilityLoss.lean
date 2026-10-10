import OAI.NumberTheory.JointDickman.Amplification.IndependentRegularityLoss
import OAI.NumberTheory.JointDickman.Counting.CoefficientDomination

namespace OAI

/-! # Harmonic probability bounds for nonregular coefficient pairs -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
noncomputable def coefficientPairFailureMass (B L : ℕ) (τ C : ℝ) (a c : ℕ) : ℝ :=
  if RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c) then 0
  else primeProductMass (auxiliaryPrimes B) (1 / 2) a *
    primeProductMass (auxiliaryPrimes B) (1 / 2) c

theorem auxiliaryHalfMass_nonneg (B n : ℕ) :
    0 ≤ primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  classical
  unfold primeProductMass
  apply sum_nonneg
  intro S hS
  split_ifs
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    exact ⟨div_nonneg (by norm_num) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

theorem coefficientPairFailureMass_nonneg (B L : ℕ) (τ C : ℝ) (a c : ℕ) :
    0 ≤ coefficientPairFailureMass B L τ C a c := by
  unfold coefficientPairFailureMass
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (auxiliaryHalfMass_nonneg B a) (auxiliaryHalfMass_nonneg B c)

theorem coefficientPairFailureMass_le {B L a c : ℕ} {τ C D : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hma : primeProductMass (auxiliaryPrimes B) (1 / 2) a ≤
      D * coefficientWeight B a / ((B : ℝ) * a))
    (hmc : primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D * coefficientWeight B c / ((B : ℝ) * c)) (hD : 0 ≤ D) :
    coefficientPairFailureMass B L τ C a c ≤
      D^2 / ((B : ℝ)^2 * a * c) *
        (coefficientWeight B a * coefficientWeight B c -
          regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c) := by
  classical
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  by_cases hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B a) ∧
      RegularPrimeSet B L τ C (coefficientPrimeSet B c)
  · simp only [coefficientPairFailureMass, ite_eq_left hreg, regularCoefficientWeight,
      ite_eq_left hreg.1, ite_eq_left hreg.2, sub_self, mul_zero, le_refl]
  · have hzero : regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c = 0 := by
      unfold regularCoefficientWeight
      split_ifs with ha hc
      · exact False.elim (hreg ⟨ha, hc⟩)
      all_goals ring
    rw [coefficientPairFailureMass, ite_eq_right hreg, hzero, sub_zero]
    calc
      _ ≤ (D * coefficientWeight B a / ((B : ℝ) * a)) *
          (D * coefficientWeight B c / ((B : ℝ) * c)) :=
        mul_le_mul hma hmc (auxiliaryHalfMass_nonneg B c)
          (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B a)) (mul_nonneg hB0.le ha0.le))
      _ = _ := by field_simp

theorem coefficient_pair_loss_nonneg (B L : ℕ) (τ C : ℝ) (a c : ℕ) :
    0 ≤ coefficientWeight B a * coefficientWeight B c -
      regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c := by
  exact sub_nonneg.mpr (mul_le_mul (regularCoefficientWeight_le B L τ C a)
    (regularCoefficientWeight_le B L τ C c) (regularCoefficientWeight_nonneg B L τ C c)
    (coefficientWeight_nonneg B a))

/-- The probability loss in one size-and-ratio box is O(B⁻²), with the
same vanishing and tail-cutoff errors as the arithmetic regularity bound. -/
theorem coefficient_failure_box_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T X : ℕ), 0 ≤ C → 0 < T →
          Real.exp (δ * B) ≤ X →
          (4 * T * X : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
          (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
            coefficientPairFailureMass B L τ C a c) ≤
            K / (B : ℝ)^2 * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨D, hD, hdom⟩ := primeProductMass_coefficient_domination hM
  obtain ⟨K, hK, hloss⟩ := independent_coefficient_regularity_loss hFord hM hδ hδ32
  refine ⟨3 * D^2 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hloss L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, hdom, eventually_gt_atTop 0] with B hl hd hB
  intro C T X hC hT hX hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hX0 : (0 : ℝ) < X := (Real.exp_pos _).trans_le hX
  have hXnat : 0 < X := by exact_mod_cast hX0
  have hlen : Real.exp (δ * B) ≤ ((4 * T * X : ℕ) : ℝ) - (T * X : ℕ) := by
    push_cast
    nlinarith only [hX, mul_le_mul_of_nonneg_right hT1 hX0.le]
  have hsum := hl C (T * X) (4 * T * X) X (2 * X) hC (by nlinarith) (by omega)
    hlen (by push_cast; linarith only [hX])
  let E := ε B + Real.exp (-(1 / 10 : ℝ) * C)
  have hprob : (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
      coefficientPairFailureMass B L τ C a c) ≤
      D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
          (coefficientWeight B a * coefficientWeight B c -
            regularCoefficientWeight B L τ C a * regularCoefficientWeight B L τ C c)) := by
    simp only [mul_sum]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro c hc
    have ha' := mem_Ico.mp ha
    have hc' := mem_Ico.mp hc
    have ha0 : 0 < a := lt_of_lt_of_le (Nat.mul_pos hT hXnat) ha'.1
    have hc0 : 0 < c := hXnat.trans_le hc'.1
    have hasize : (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) :=
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ (4 * T * X : ℝ)).trans hsize
    have hcsize : (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
      have hh : (c : ℝ) ≤ 2 * X := by exact_mod_cast hc'.2.le
      exact hh.trans ((by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0.le] :
        (2 * X : ℝ) ≤ 4 * T * X).trans hsize)
    apply (coefficientPairFailureMass_le hB ha0 hc0 (hd a ha0 hasize) (hd c hc0 hcsize) hD.le).trans
    apply mul_le_mul_of_nonneg_right _ (coefficient_pair_loss_nonneg B L τ C a c)
    apply div_le_div_of_nonneg_left (sq_nonneg D) (by positivity)
    have haR : (T * X : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hcR : (X : ℝ) ≤ c := by exact_mod_cast hc'.1
    gcongr
  calc
    _ ≤ _ := hprob
    _ ≤ D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (K * (((4 * T * X : ℕ) : ℝ) - (T * X : ℕ)) * (((2 * X : ℕ) : ℝ) - X) * E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      dsimp only [E]
      push_cast
      field_simp
      ring

end JointDickman

end OAI
