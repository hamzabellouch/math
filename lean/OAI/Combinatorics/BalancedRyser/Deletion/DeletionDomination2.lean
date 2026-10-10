import OAI.Combinatorics.BalancedRyser.Deletion.DeletionDomination
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionLawNormalization
import OAI.Combinatorics.BalancedRyser.Deletion.DeletionMassBound
import OAI.Combinatorics.BalancedRyser.Deletion.ExponentialDomination

namespace OAI

namespace Balanced.DeletionLaw

theorem atom_le_of_cylinder {q n : ℕ} {κ : Weight q n} {K : ℝ}
    (h : CylinderBound κ K) (m₀ m₁ : Offset q n) (s : Split q n) :
    κ m₀ m₁ s ≤ (K / q) ^ (2 * n) := by
  classical
  have hc := h m₀ m₁ Finset.univ (fun t => s t.1 t.2)
  have heq : ∀ s' : Split q n,
      (∀ t ∈ (Finset.univ : Finset (Fin 2 × Fin n)),
        s' t.1 t.2 = s t.1 t.2) ↔ s' = s := by
    intro s'
    simp only [Finset.mem_univ, forall_const]
    constructor
    · intro hs
      funext j i
      exact hs (j, i)
    · rintro rfl
      exact fun _ => rfl
  simp_rw [heq] at hc
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using hc

theorem six_mul_choose_three_le (q : ℕ) :
    6 * (Nat.choose q 3 : ℝ) ≤ (q : ℝ) ^ 3 := by
  have h := (Nat.choose_le_pow_div (α := ℝ) 3 q)
  norm_num at h
  linarith

theorem assignment_normalization_le {q : ℕ} (hq : 3 ≤ q) :
    6 / (q : ℝ) ^ 3 ≤ (Nat.choose q 3 : ℝ)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcpos : (0 : ℝ) < Nat.choose q 3 := by
    exact_mod_cast Nat.choose_pos hq
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (pow_pos hqpos 3) hcpos).2
  simpa using six_mul_choose_three_le q

theorem assignment_factorization (q n : ℕ) (K : ℝ) :
    (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) =
      (6 * K ^ 2 / (q : ℝ) ^ 3) ^ n := by
  rw [pow_mul, div_pow, ← div_pow, ← mul_pow]
  congr 1
  ring

theorem assignment_bound_le_uniform {q n : ℕ} (hq : 3 ≤ q) (K : ℝ) :
    (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) ≤
      K ^ (2 * n) * uniformDeletionMass q n := by
  rw [assignment_factorization]
  have hb : 6 * K ^ 2 / (q : ℝ) ^ 3 ≤
      K ^ 2 * (Nat.choose q 3 : ℝ)⁻¹ := by
    calc
      6 * K ^ 2 / (q : ℝ) ^ 3 = K ^ 2 * (6 / (q : ℝ) ^ 3) := by ring
      _ ≤ K ^ 2 * (Nat.choose q 3 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (assignment_normalization_le hq) (sq_nonneg K)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 6 * K ^ 2 / (q : ℝ) ^ 3) hb n
  simpa only [mul_pow, ← pow_mul, inv_pow, uniformDeletionMass] using hp

theorem conditioned_bound_of_joint {q n : ℕ} {κ : Weight q n} {K a₀ : ℝ}
    (ha₀ : 0 < a₀) (hsuccess : a₀ ≤ successMass κ)
    (D : DeletionSet q n)
    (hjoint : deletionMass κ D ≤ K ^ (2 * n) * uniformDeletionMass q n) :
    conditionedDeletionMass κ D ≤ a₀⁻¹ * K ^ (2 * n) * uniformDeletionMass q n := by
  have hspos : 0 < successMass κ := ha₀.trans_le hsuccess
  have hnonneg : 0 ≤ K ^ (2 * n) * uniformDeletionMass q n := by
    apply mul_nonneg
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg K) n
    · unfold uniformDeletionMass
      positivity
  unfold conditionedDeletionMass
  calc
    deletionMass κ D / successMass κ ≤
        (K ^ (2 * n) * uniformDeletionMass q n) / successMass κ :=
      div_le_div_of_nonneg_right hjoint hspos.le
    _ ≤ (K ^ (2 * n) * uniformDeletionMass q n) / a₀ :=
      div_le_div_of_nonneg_left hnonneg ha₀ hsuccess
    _ = a₀⁻¹ * K ^ (2 * n) * uniformDeletionMass q n := by ring

theorem six_mul_choose_three_eq {q : ℕ} (hq : 3 ≤ q) :
    6 * (Nat.choose q 3 : ℝ) = (q : ℝ) * (q - 1) * (q - 2) := by
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have h := congrArg (fun x : ℕ => (x : ℝ))
    (Nat.descFactorial_eq_factorial_mul_choose q 3)
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.cast_sub hq1, Nat.cast_sub hq2] at h
  nlinarith [h]

theorem assignment_ratio_exact {q n : ℕ} (hq : 3 ≤ q) (K : ℝ) :
    ((6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n)) /
        uniformDeletionMass q n =
      (K ^ 2 * (1 - 1 / q) * (1 - 2 / q)) ^ n := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [assignment_factorization, uniformDeletionMass, div_inv_eq_mul, ← mul_pow]
  congr 1
  have hc := six_mul_choose_three_eq hq
  field_simp
  nlinarith [hc]

theorem conditioned_ratio_of_assignment_bound {q n : ℕ} (hq : 3 ≤ q)
    {κ : Weight q n} {K a₀ : ℝ} (ha₀ : 0 < a₀)
    (hsuccess : a₀ ≤ successMass κ) (D : DeletionSet q n)
    (hjoint : deletionMass κ D ≤
      (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n)) :
    conditionedDeletionMass κ D / uniformDeletionMass q n ≤
      a₀⁻¹ * (K ^ 2 * (1 - 1 / q) * (1 - 2 / q)) ^ n := by
  have hspos : 0 < successMass κ := ha₀.trans_le hsuccess
  have hupos : 0 < uniformDeletionMass q n := by
    unfold uniformDeletionMass
    have hc : (0 : ℝ) < Nat.choose q 3 := by exact_mod_cast Nat.choose_pos hq
    positivity
  have hA : 0 ≤ (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) := by
    rw [assignment_factorization]
    positivity
  have hcond : conditionedDeletionMass κ D ≤
      ((6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n)) / a₀ := by
    unfold conditionedDeletionMass
    exact (div_le_div_of_nonneg_right hjoint hspos.le).trans
      (div_le_div_of_nonneg_left hA ha₀ hsuccess)
  calc
    conditionedDeletionMass κ D / uniformDeletionMass q n ≤
        (((6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n)) / a₀) /
          uniformDeletionMass q n := div_le_div_of_nonneg_right hcond hupos.le
    _ = a₀⁻¹ * (((6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n)) /
          uniformDeletionMass q n) := by ring
    _ = a₀⁻¹ * (K ^ 2 * (1 - 1 / q) * (1 - 2 / q)) ^ n := by
      rw [assignment_ratio_exact hq]

theorem deletionMass_le_assignment_bound {q n : ℕ} (hq : 0 < q)
    {κ : Weight q n} {K : ℝ} (hK : 0 ≤ K)
    (hκ : IsSubprobabilityKernel κ) (hcyl : CylinderBound κ K)
    (D : DeletionSet q n) (hD : ∀ i, (D i).card = 3) :
    deletionMass κ D ≤ (6 : ℝ) ^ n * ((K / q) ^ (2 * n) / (q : ℝ) ^ n) := by
  apply deletionMass_le_of_offsetAverage_le κ hκ.1 D hD
  · positivity
  · intro m₁ s
    exact offsetAverage_le_of_atom_bound hq ((K / q) ^ (2 * n))
      (atom_le_of_cylinder hcyl) m₁ s

theorem finite_domination : FiniteDomination := by
  intro q n hq κ K a₀ hK ha₀ hκ _hdistinct hcyl hsuccess D hD
  apply conditioned_bound_of_joint ha₀ hsuccess D
  exact (deletionMass_le_assignment_bound (by omega) hK hκ hcyl D hD).trans
    (assignment_bound_le_uniform hq K)

theorem exponential_domination : ExponentialDomination := by
  intro K a₀ hK ha₀
  refine ⟨a₀⁻¹ + 4 * K,
    BalancedRyser.deletion_ratio_exponential_coefficient_pos ha₀ hK, ?_⟩
  intro q hq κ hκ hdistinct hcyl hsuccess D
  by_cases hD : ∀ i, (D i).card = 3
  · rw [uniformDeletionLaw, ite_eq_left hD]
    have hf := finite_domination q (q + 1) hq κ K a₀ hK ha₀ hκ hdistinct hcyl hsuccess D hD
    apply hf.trans
    exact mul_le_mul_of_nonneg_right
      (BalancedRyser.deletion_ratio_exponential_envelope ha₀ hK (by omega))
      (by unfold uniformDeletionMass; positivity)
  · rw [conditionedDeletionMass_eq_zero_of_invalid hκ hdistinct D hD,
      uniformDeletionLaw, ite_eq_right hD, mul_zero]

end Balanced.DeletionLaw

end OAI
