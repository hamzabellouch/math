import OAI.NumberTheory.JointDickman.Amplification.MixedThreeFormLocal
import OAI.NumberTheory.JointDickman.Arithmetic.ThreeFormSieve

namespace OAI

/-! # The rectangle sieve for three separately tilted coefficient weights -/

namespace JointDickman

open Finset

noncomputable def mixedThreeFormLocalFactor (p j : ℕ) (t u v : ℝ) : ℝ :=
  (∑ b ∈ range p, ∑ c ∈ range p,
    residueWeight t 0 (b : ZMod p) * residueWeight u 0 (c : ZMod p) *
      residueWeight v 0 ((b : ZMod p) + j * c)) / (p : ℝ) ^ 2

theorem mixedThreeFormLocalFactor_eq {p : ℕ} [NeZero p] (j : ℕ) (t u v : ℝ) :
    mixedThreeFormLocalFactor p j t u v = mixedThreeFormMean (j : ZMod p) t u v := by
  unfold mixedThreeFormLocalFactor mixedThreeFormMean
  rw [real_residue_double_sum_eq_range]

theorem mixedThreeFormLocalFactor_nonneg (p j : ℕ) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ mixedThreeFormLocalFactor p j t u v := by
  unfold mixedThreeFormLocalFactor
  exact div_nonneg (sum_nonneg (fun _b _ => sum_nonneg (fun _c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ hu))
      (residueWeight_nonneg _ _ hv)))) (sq_nonneg _)

open Classical in
theorem mixed_three_form_local_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t u v : ℕ → ℝ) (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    (hu : ∀ p ∈ P, 0 ≤ u p ∧ u p ≤ 1) (hv : ∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1)
    {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P, mixedThreeFormLocalFactor p j (t p) (u p) (v p)) ≤
      (∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
        (∏ p ∈ P, (1 - (1 - v p) / p)) * singularFactor 24 j := by
  have hlocal (p : ℕ) (hp : p ∈ P) : mixedThreeFormLocalFactor p j (t p) (u p) (v p) ≤
      (1 - (1 - t p) / p) * (1 - (1 - u p) / p) * (1 - (1 - v p) / p) *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    rw [mixedThreeFormLocalFactor_eq]
    simpa only [ZMod.natCast_eq_zero_iff] using mixedThreeFormMean_bound (j : ZMod p)
      (ht p hp).1 (ht p hp).2 (hu p hp).1 (hu p hp).2 (hv p hp).1 (hv p hp).2
  have hs (f : ℕ → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p) (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - (1 - f p) / p := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [hf p hp]
  have hexcept : (∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1) ≤ singularFactor 24 j := by
    rw [← prod_filter]
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
    · intros; positivity
    · intro p _ _
      exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∏ p ∈ P, (1 - (1 - t p) / p) * (1 - (1 - u p) / p) * (1 - (1 - v p) / p) *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := prod_le_prod₀
      (fun p hp => mixedThreeFormLocalFactor_nonneg p j (ht p hp).1 (hu p hp).1 (hv p hp).1) hlocal
    _ = (∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
        (∏ p ∈ P, (1 - (1 - v p) / p)) * ∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1 := by
      simp only [prod_mul_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexcept
      (mul_nonneg (mul_nonneg (prod_nonneg (hs t (fun p hp => (ht p hp).1)))
        (prod_nonneg (hs u (fun p hp => (hu p hp).1))))
          (prod_nonneg (hs v (fun p hp => (hv p hp).1))))

noncomputable def mixedThreeFormSieveWeight (P : Finset ℕ) (t u v : ℕ → ℝ) (j b c : ℕ) : ℝ :=
  ∏ p ∈ P, residueWeight (t p) 0 (b : ZMod p) * residueWeight (u p) 0 (c : ZMod p) *
    residueWeight (v p) 0 ((b : ZMod p) + j * c)

theorem mixed_three_form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (t u v : ℕ → ℝ)
      (j l₁ r₁ l₂ r₂ Z : ℕ), j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 6 ≤ p) →
      (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) →
      (∀ p ∈ P, 0 ≤ u p ∧ u p ≤ 1) →
      (∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1) →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂, mixedThreeFormSieveWeight P t u v j b c) ≤
        C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) *
          ((∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
            (∏ p ∈ P, (1 - (1 - v p) / p))) * singularFactor 24 j +
          2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := affine_rectangle_sieve hFord hM (by norm_num : 0 < (3 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P t u v j l₁ r₁ l₂ r₂ Z hj hI hJ hZ hP ht hu hv
  classical
  let a : (p : P) → Fin 3 → ZMod p.val := fun _ => ![1, 0, 1]
  let b : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 1, j]
  let c : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 0, 0]
  let θ : P → Fin 3 → ℝ := fun p => ![t p.val, u p.val, v p.val]
  have hproper (p : P) (i : Fin 3) : a p i ≠ 0 ∨ b p i ≠ 0 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    fin_cases i <;> simp [a, b]
  have hθ (p : P) (i : Fin 3) : 0 ≤ θ p i ∧ θ p i ≤ 1 := by
    fin_cases i
    · exact ht p.val p.property
    · exact hu p.val p.property
    · exact hv p.val p.property
  have heq (p : P) (r s : ZMod p.val) :
      affineFormWeight (a p) (b p) (c p) (θ p) r s =
        residueWeight (t p.val) 0 r * residueWeight (u p.val) 0 s *
          residueWeight (v p.val) 0 (r + j * s) := by
    simp [affineFormWeight, a, b, c, θ, Fin.prod_univ_succ, residueWeight, mul_assoc]
    split_ifs <;> rfl
  have hh := hbound P a b c θ l₁ r₁ l₂ r₂ Z hI hJ hZ hP hproper hθ
  simp_rw [heq] at hh
  have hweight (r s : ℕ) : (∏ p : P, residueWeight (t p.val) 0 (r : ZMod p.val) *
      residueWeight (u p.val) 0 (s : ZMod p.val) *
        residueWeight (v p.val) 0 ((r : ZMod p.val) + j * s)) = mixedThreeFormSieveWeight P t u v j r s :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (t p) 0 (r : ZMod p) *
      residueWeight (u p) 0 (s : ZMod p) * residueWeight (v p) 0 ((r : ZMod p) + j * s))
  simp_rw [hweight] at hh
  change _ ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) *
    (∏ p : P, mixedThreeFormLocalFactor p.val j (t p.val) (u p.val) (v p.val)) + _ at hh
  rw [P.prod_coe_sort (fun p : ℕ => mixedThreeFormLocalFactor p j (t p) (u p) (v p))] at hh
  refine hh.trans (add_le_add ?_ le_rfl)
  have hprod := mixed_three_form_local_product_bound P (fun p hp => (hP p hp).1) t u v ht hu hv hj
  have harea : 0 ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) :=
    mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast hI)))
      (sub_nonneg.mpr (by exact_mod_cast hJ))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod harea

end JointDickman

end OAI
