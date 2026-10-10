import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import OAI.Analysis.MarkovType.FiniteWeightedHolder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

omit sectionNormedSpaceℝE in
theorem finiteL2Norm_eq_rpow [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ f = (μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ))) ^ (1 / (2 : ℝ)) :=
  Real.sqrt_eq_rpow _

theorem finiteL2Norm_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → E) :
    finiteL2Norm μ (fun ω => c • f ω) = |c| * finiteL2Norm μ f := by
  apply (sq_eq_sq₀ (finiteL2Norm_nonneg μ _)
    (mul_nonneg (abs_nonneg c) (finiteL2Norm_nonneg μ f))).1
  rw [finiteL2Norm_sq, mul_pow, finiteL2Norm_sq]
  simp only [FiniteLaw.expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [norm_smul, Real.norm_eq_abs, mul_pow]
  ring

@[simp] theorem finiteL2Norm_neg (μ : FiniteLaw Ω) (f : Ω → E) :
    finiteL2Norm μ (fun ω => -f ω) = finiteL2Norm μ f := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
    finiteL2Norm_smul μ (-1) f

omit sectionNormedSpaceℝE in
theorem finite_norm_product_le_L2_mul_L2 [NormedSpace ℝ E] (μ : FiniteLaw Ω) (f g : Ω → E) :
    μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) ≤ finiteL2Norm μ f * finiteL2Norm μ g := by
  have h := finite_weighted_holder_univ
    (w := μ.mass) (a := fun ω => ‖f ω‖) (b := fun ω => ‖g ω‖)
    Real.HolderConjugate.two_two μ.mass_nonneg (fun ω => norm_nonneg _)
    (fun ω => norm_nonneg _)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, finiteL2Norm,
    FiniteLaw.expect, mul_assoc] using h

theorem finiteL2Norm_add_le (μ : FiniteLaw Ω) (f g : Ω → E) :
    finiteL2Norm μ (fun ω => f ω + g ω) ≤ finiteL2Norm μ f + finiteL2Norm μ g := by
  have hcross := finite_norm_product_le_L2_mul_L2 μ f g
  have hexpand : μ.expect (fun ω => (‖f ω‖ + ‖g ω‖) ^ (2 : ℕ)) =
      μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) +
        2 * μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) +
          μ.expect (fun ω => ‖g ω‖ ^ (2 : ℕ)) := by
    simp only [FiniteLaw.expect]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    ring
  have hsquare : finiteL2Norm μ (fun ω => f ω + g ω) ^ (2 : ℕ) ≤
      (finiteL2Norm μ f + finiteL2Norm μ g) ^ (2 : ℕ) := by
    calc
      _ = μ.expect (fun ω => ‖f ω + g ω‖ ^ (2 : ℕ)) := finiteL2Norm_sq μ _
      _ ≤ μ.expect (fun ω => (‖f ω‖ + ‖g ω‖) ^ (2 : ℕ)) :=
        μ.expect_mono (fun ω => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
      _ = finiteL2Norm μ f ^ (2 : ℕ) +
          2 * μ.expect (fun ω => ‖f ω‖ * ‖g ω‖) +
            finiteL2Norm μ g ^ (2 : ℕ) := by
        rw [hexpand, finiteL2Norm_sq, finiteL2Norm_sq]
      _ ≤ _ := by nlinarith only [hcross]
  exact (sq_le_sq₀ (finiteL2Norm_nonneg μ _)
    (add_nonneg (finiteL2Norm_nonneg μ f) (finiteL2Norm_nonneg μ g))).1 hsquare

theorem finiteL2Norm_sub_le (μ : FiniteLaw Ω) (f g : Ω → E) :
    finiteL2Norm μ (fun ω => f ω - g ω) ≤ finiteL2Norm μ f + finiteL2Norm μ g := by
  simpa only [sub_eq_add_neg, finiteL2Norm_neg] using
    finiteL2Norm_add_le μ f (fun ω => -g ω)

theorem finiteL2Norm_sum_le {ι : Type*} (μ : FiniteLaw Ω)
    (s : Finset ι) (f : ι → Ω → E) :
    finiteL2Norm μ (fun ω => ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, finiteL2Norm μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finiteL2Norm_zero, le_refl]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (finiteL2Norm_add_le μ (f i) (fun ω => ∑ j ∈ s, f j ω)).trans
        (add_le_add_right ih _)

theorem finiteL2Norm_mono (μ : FiniteLaw Ω) (f g : Ω → E)
    (hfg : ∀ ω, ‖f ω‖ ≤ ‖g ω‖) : finiteL2Norm μ f ≤ finiteL2Norm μ g := by
  apply (sq_le_sq₀ (finiteL2Norm_nonneg μ f) (finiteL2Norm_nonneg μ g)).1
  rw [finiteL2Norm_sq, finiteL2Norm_sq]
  exact μ.expect_mono (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hfg ω) 2)

theorem finiteL2Norm_le_of_pointwise (μ : FiniteLaw Ω) (f : Ω → E)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ ω, ‖f ω‖ ≤ B) : finiteL2Norm μ f ≤ B := by
  apply (sq_le_sq₀ (finiteL2Norm_nonneg μ f) hB).1
  rw [finiteL2Norm_sq]
  calc
    μ.expect (fun ω => ‖f ω‖ ^ (2 : ℕ)) ≤ μ.expect (fun _ => B ^ (2 : ℕ)) :=
      μ.expect_mono (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hf ω) 2)
    _ = B ^ (2 : ℕ) := μ.expect_const _

theorem eq_zero_of_finiteL2Norm_eq_zero (μ : FiniteLaw Ω) (f : Ω → E)
    (h0 : finiteL2Norm μ f = 0) (ω : Ω) (hω : 0 < μ.mass ω) : f ω = 0 := by
  have hsum : (∑ η, μ.mass η * ‖f η‖ ^ (2 : ℕ)) = 0 := by
    have h := finiteL2Norm_sq μ f
    rw [h0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact h.symm
  have hle : μ.mass ω * ‖f ω‖ ^ (2 : ℕ) ≤ ∑ η, μ.mass η * ‖f η‖ ^ (2 : ℕ) :=
    Finset.single_le_sum (fun η _ => mul_nonneg (μ.mass_nonneg η) (sq_nonneg ‖f η‖))
      (Finset.mem_univ ω)
  have hterm : μ.mass ω * ‖f ω‖ ^ (2 : ℕ) = 0 :=
    le_antisymm (hle.trans_eq hsum) (mul_nonneg (μ.mass_nonneg ω) (sq_nonneg _))
  have hnorm : ‖f ω‖ ^ (2 : ℕ) = 0 := (mul_eq_zero.mp hterm).resolve_left hω.ne'
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm)

end MarkovSuperreflexivity

end

end OAI
