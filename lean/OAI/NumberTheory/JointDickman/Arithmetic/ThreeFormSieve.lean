import OAI.NumberTheory.JointDickman.Amplification.ThreeFormLocalBound
import OAI.NumberTheory.JointDickman.Amplification.SingularFactor

namespace OAI

/-! # The three-form rectangle sieve with its singular factor -/

namespace JointDickman

open Finset

theorem real_residue_sum_eq_range {p : ℕ} [NeZero p] (f : ZMod p → ℝ) :
    (∑ r : ZMod p, f r) = ∑ n ∈ range p, f n := by
  have h := residue_sum_eq_range (fun r => (f r : ℂ))
  exact_mod_cast h

theorem real_residue_double_sum_eq_range {p : ℕ} [NeZero p]
    (f : ZMod p → ZMod p → ℝ) :
    (∑ r : ZMod p, ∑ s : ZMod p, f r s) =
      ∑ m ∈ range p, ∑ n ∈ range p, f m n := by
  rw [real_residue_sum_eq_range]
  apply sum_congr rfl
  intro m _
  exact real_residue_sum_eq_range _

noncomputable def threeFormLocalFactor (p j : ℕ) (t : ℝ) : ℝ :=
  (∑ b ∈ range p, ∑ c ∈ range p,
    residueWeight t 0 (b : ZMod p) * residueWeight t 0 (c : ZMod p) *
      residueWeight t 0 ((b : ZMod p) + j * c)) / (p : ℝ) ^ 2

theorem threeFormLocalFactor_eq_mean {p : ℕ} [NeZero p] (j : ℕ) (t : ℝ) :
    threeFormLocalFactor p j t = threeFormResidueMean (j : ZMod p) t := by
  unfold threeFormLocalFactor threeFormResidueMean
  rw [real_residue_double_sum_eq_range]

theorem threeFormLocalFactor_nonneg (p j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ threeFormLocalFactor p j t := by
  unfold threeFormLocalFactor
  exact div_nonneg (sum_nonneg (fun b _ => sum_nonneg (fun c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ ht))
      (residueWeight_nonneg _ _ ht)))) (sq_nonneg _)

open Classical in
theorem three_form_local_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (θ : ℕ → ℝ) (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P, threeFormLocalFactor p j (θ p)) ≤
      (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 * singularFactor 24 j := by
  have hlocal (p : ℕ) (hp : p ∈ P) : threeFormLocalFactor p j (θ p) ≤
      (1 - (1 - θ p) / p) ^ 3 * (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    rw [threeFormLocalFactor_eq_mean]
    simpa only [ZMod.natCast_eq_zero_iff] using
      threeFormResidueMean_bound (j : ZMod p) (hθ p hp).1 (hθ p hp).2
  have hs (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 - (1 - θ p) / p := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [(hθ p hp).1]
  have hexcept : (∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1) ≤
      singularFactor 24 j := by
    rw [← prod_filter]
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
    · intro p _
      positivity
    · intro p _ _
      exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∏ p ∈ P, (1 - (1 - θ p) / p) ^ 3 *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) :=
      prod_le_prod₀ (fun p hp => threeFormLocalFactor_nonneg p j (hθ p hp).1) hlocal
    _ = (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 *
        ∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1 := by
      rw [prod_mul_distrib, prod_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexcept (pow_nonneg (prod_nonneg hs) _)

noncomputable def threeFormSieveWeight (P : Finset ℕ) (θ : ℕ → ℝ) (j b c : ℕ) : ℝ :=
  ∏ p ∈ P, residueWeight (θ p) 0 (b : ZMod p) * residueWeight (θ p) 0 (c : ZMod p) *
    residueWeight (θ p) 0 ((b : ZMod p) + j * c)

/-- The actual three-form sieve, with a separated singular factor and
an explicit polynomial remainder. -/
theorem three_form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ)
      (j u v w x Z : ℕ), j ≠ 0 → u ≤ v → w ≤ x → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 6 ≤ p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ b ∈ Ico u v, ∑ c ∈ Ico w x, threeFormSieveWeight P θ j b c) ≤
        C * ((v : ℝ) - u) * ((x : ℝ) - w) *
          (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 3 * singularFactor 24 j +
        2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := affine_rectangle_sieve hFord hM (by norm_num : 0 < (3 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ j u v w x Z hj huv hwx hZ hP hθ
  classical
  let a : (p : P) → Fin 3 → ZMod p.val := fun _ => ![1, 0, 1]
  let b : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 1, j]
  let c : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 0, 0]
  let t : P → Fin 3 → ℝ := fun p _ => θ p.val
  have hproper (p : P) (i : Fin 3) : a p i ≠ 0 ∨ b p i ≠ 0 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    fin_cases i <;> simp [a, b]
  have heq (p : P) (r s : ZMod p.val) :
      affineFormWeight (a p) (b p) (c p) (t p) r s =
        residueWeight (θ p.val) 0 r * residueWeight (θ p.val) 0 s *
          residueWeight (θ p.val) 0 (r + j * s) := by
    simp [affineFormWeight, a, b, c, t, Fin.prod_univ_succ, residueWeight, mul_assoc]
    split_ifs <;> rfl
  have hh := hbound P a b c t u v w x Z huv hwx hZ hP hproper (fun p _ => hθ p.val p.property)
  simp_rw [heq] at hh
  have hweight (r s : ℕ) : (∏ p : P, residueWeight (θ p.val) 0 (r : ZMod p.val) *
      residueWeight (θ p.val) 0 (s : ZMod p.val) *
        residueWeight (θ p.val) 0 ((r : ZMod p.val) + j * s)) = threeFormSieveWeight P θ j r s :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (θ p) 0 (r : ZMod p) *
      residueWeight (θ p) 0 (s : ZMod p) * residueWeight (θ p) 0 ((r : ZMod p) + j * s))
  simp_rw [hweight] at hh
  change _ ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) *
    (∏ p : P, threeFormLocalFactor p.val j (θ p.val)) + _ at hh
  rw [P.prod_coe_sort (fun p : ℕ => threeFormLocalFactor p j (θ p))] at hh
  refine hh.trans (add_le_add ?_ le_rfl)
  have hprod := three_form_local_product_bound P (fun p hp => (hP p hp).1) θ hθ hj
  have harea : 0 ≤ C * ((v : ℝ) - u) * ((x : ℝ) - w) := by
    apply mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast huv)))
      (sub_nonneg.mpr (by exact_mod_cast hwx))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod harea

end JointDickman

end OAI
