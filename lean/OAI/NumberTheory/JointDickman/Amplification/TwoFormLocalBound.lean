import OAI.NumberTheory.JointDickman.Amplification.AffineLocalFactors
import OAI.NumberTheory.JointDickman.Arithmetic.FormIntervalSieve
import OAI.NumberTheory.JointDickman.Arithmetic.ThreeFormSieve

namespace OAI

/-! # Two distinct affine roots and their weighted interval bound -/

namespace JointDickman

open Finset

theorem sum_two_residueWeights_bound {p : ℕ} [NeZero p]
    (t : ℝ) (a b : ZMod p) (hab : a ≠ b) :
    (∑ x : ZMod p, residueWeight t a x * residueWeight t b x) / p ≤
      (1 - (1 - t) / p) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [sum_two_residueWeights t t a b hab, ZMod.card]
  have heq : (1 - (1 - t) / (p : ℝ)) ^ 2 - ((p : ℝ) - 2 + t + t) / p =
      ((1 - t) / p) ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg ((1 - t) / (p : ℝ))]

theorem affine_residue_root {p : ℕ} [Fact p.Prime] (b j x : ZMod p) (hj : j ≠ 0) :
    b + j * x = 0 ↔ x = -b / j := by
  rw [eq_div_iff hj]
  constructor <;> intro h <;> linear_combination h

open Classical in
theorem formRootWeight_two {p : ℕ} (a b x : ZMod p) (t : ℝ) :
    formRootWeight ![a, b] (fun _ => t) x = residueWeight t a x * residueWeight t b x := by
  unfold formRootWeight
  rw [prod_filter, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, residueWeight]
  apply congrArg₂ (fun u v : ℝ => u * v)
  · exact @ite_cond_congr ℝ (a = x) (x = a) _ (Classical.propDecidable (x = a)) t 1 (propext eq_comm)
  · exact @ite_cond_congr ℝ (b = x) (x = b) _ (Classical.propDecidable (x = b)) t 1 (propext eq_comm)

theorem two_form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ) (j b u v Z : ℕ),
      u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p ∧ ¬ p ∣ j ∧ ¬ p ∣ b) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) + j * n)) ≤
        C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := form_interval_sieve hFord hM (by norm_num : 0 < (2 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ j b u v Z huv hZ hP hθ
  classical
  let : ∀ p : P, Fact p.val.Prime := fun p => ⟨(hP p.val p.property).1⟩
  let root : (p : P) → Fin 2 → ZMod p.val := fun p => ![0, -(b : ZMod p.val) / (j : ZMod p.val)]
  let t : P → Fin 2 → ℝ := fun p _ => θ p.val
  have hroot (p : P) : (0 : ZMod p.val) ≠ -(b : ZMod p.val) / (j : ZMod p.val) := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have hb : (b : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.2
    have hj : (j : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.1
    exact (div_ne_zero (neg_ne_zero.mpr hb) hj).symm
  have heq (p : P) (x : ZMod p.val) : formRootWeight (root p) (t p) x =
      residueWeight (θ p.val) 0 x * residueWeight (θ p.val) 0 ((b : ZMod p.val) + j * x) := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have hj : (j : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.1
    change formRootWeight ![0, -(b : ZMod p.val) / (j : ZMod p.val)] (fun _ => θ p.val) x = _
    rw [formRootWeight_two]
    congr 1
    by_cases hx : x = -(b : ZMod p.val) / (j : ZMod p.val)
    · simp [residueWeight, affine_residue_root _ _ _ hj, hx]
    · simp [residueWeight, affine_residue_root _ _ _ hj, hx]
  have hmean (p : P) : (∑ x ∈ range p.val, formRootWeight (root p) (t p) (x : ZMod p.val)) / p.val ≤
      (1 - (1 - θ p.val) / p.val) ^ 2 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have h := sum_two_residueWeights_bound (θ p.val) (0 : ZMod p.val)
      (-(b : ZMod p.val) / (j : ZMod p.val)) (hroot p)
    rw [real_residue_sum_eq_range] at h
    have hpoint (x : ZMod p.val) : formRootWeight (root p) (t p) x =
        residueWeight (θ p.val) 0 x * residueWeight (θ p.val) (-(b : ZMod p.val) / (j : ZMod p.val)) x := by
      exact formRootWeight_two _ _ _ _
    simpa only [hpoint] using h
  have hh := hbound P root t u v Z huv hZ
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1⟩)
    (fun p _ => hθ p.val p.property)
  simp_rw [heq] at hh
  have hprod : (∏ p : P, (∑ x ∈ range p.val, formRootWeight (root p) (t p) (x : ZMod p.val)) / p.val) ≤
      (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 := by
    calc
      _ ≤ ∏ p : P, (1 - (1 - θ p.val) / p.val) ^ 2 := prod_le_prod₀
        (fun p _ => div_nonneg (sum_nonneg (fun x _ => by
          rw [heq]
          exact mul_nonneg (residueWeight_nonneg _ _ (hθ p.val p.property).1)
            (residueWeight_nonneg _ _ (hθ p.val p.property).1))) (Nat.cast_nonneg _))
        (fun p _ => hmean p)
      _ = _ := by rw [prod_pow, P.prod_coe_sort (fun p : ℕ => (1 - (1 - θ p) / p))]
  have hweight (n : ℕ) : (∏ p : P, residueWeight (θ p.val) 0 (n : ZMod p.val) *
      residueWeight (θ p.val) 0 ((b : ZMod p.val) + j * n)) =
      ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) * residueWeight (θ p) 0 ((b : ZMod p) + j * n) :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (θ p) 0 (n : ZMod p) *
      residueWeight (θ p) 0 ((b : ZMod p) + j * n))
  simp_rw [hweight] at hh
  simp_rw [heq] at hprod
  refine hh.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast huv)))

end JointDickman

end OAI
