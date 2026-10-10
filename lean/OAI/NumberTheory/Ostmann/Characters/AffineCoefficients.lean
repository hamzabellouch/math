import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Ostmann.Characters.AffineFibers
import OAI.NumberTheory.Ostmann.Preliminaries.TestFunctions

namespace OAI

/-!
# The affine coefficient array

The identity fiber is diagonal, and all other fibers have size at most two.
These facts give the coefficient-square estimate in equation
`tree-affine-coefficient-norm` without a pointwise bound on the function.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem norm_sum_sq_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  simpa using complex_weighted_sum_sq s (fun _ => 1) f

theorem affineParameters_eq_identity_iff {p : ℕ} [Fact p.Prime]
    (r s : (ZMod p)ˣ) : affineParameters r s = (1, 0) ↔ r = s := by
  constructor
  · intro h
    have hsquare : (s / r) ^ 2 = 1 := congrArg Prod.fst h
    have htrans := congrArg Prod.snd h
    change (r : ZMod p) * (((s / r : (ZMod p)ˣ) : ZMod p) -
      ((s / r : (ZMod p)ˣ) : ZMod p) ^ 2) = 0 at htrans
    rw [← Units.val_pow_eq_pow_val, hsquare, Units.val_one] at htrans
    have hz : (s / r : (ZMod p)ˣ) = 1 :=
      Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp htrans).resolve_left (Units.ne_zero r)))
    exact (div_eq_one.mp hz).symm
  · rintro rfl
    simp [affineParameters]

/-- The unnormalized coefficients obtained by collecting ordered unit pairs. -/
noncomputable def affineCoefficientSum {p : ℕ} [Fact p.Prime] (G : (ZMod p)ˣ → ℂ)
    (ab : (ZMod p)ˣ × ZMod p) : ℂ :=
  ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab), conj (G rs.1) * G rs.2

theorem affineCoefficientSum_identity {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) :
    affineCoefficientSum G (1, 0) = ∑ r : (ZMod p)ˣ, conj (G r) * G r := by
  classical
  simp only [affineCoefficientSum, Finset.sum_filter, affineParameters_eq_identity_iff]
  rw [Fintype.sum_prod_type]
  simp

theorem affineCoefficientSum_nonidentity_bound {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (ab : (ZMod p)ˣ × ZMod p) (hab : ab ≠ (1, 0)) :
    ‖affineCoefficientSum G ab‖ ^ 2 ≤
      2 * ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
        (fun rs => affineParameters rs.1 rs.2 = ab),
        ‖G rs.1‖ ^ 2 * ‖G rs.2‖ ^ 2 := by
  classical
  have hc : (((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab)).card : ℝ) ≤ 2 := by
    exact_mod_cast affineParameters_fiber_card_le_two ab.1 ab.2 hab
  have hn := norm_sum_sq_le_card_mul
    ((Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab))
    (fun rs => conj (G rs.1) * G rs.2)
  simp only [norm_mul, Complex.norm_conj, mul_pow] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hc
    (Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem affineCoefficientSum_sq_sum {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) :
    (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficientSum G ab‖ ^ 2) ≤
      3 * (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ^ 2 := by
  classical
  let S : ℝ := ∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2
  let w : (ZMod p)ˣ × (ZMod p)ˣ → ℝ := fun rs => ‖G rs.1‖ ^ 2 * ‖G rs.2‖ ^ 2
  let F : (ZMod p)ˣ × ZMod p → ℝ := fun ab =>
    ∑ rs ∈ (Finset.univ : Finset ((ZMod p)ˣ × (ZMod p)ˣ)).filter
      (fun rs => affineParameters rs.1 rs.2 = ab), w rs
  have hF : ∀ ab, 0 ≤ F ab := fun ab =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have htotal : ∑ ab, F ab = S ^ 2 := by
    simp only [F, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Fintype.sum_prod_type]
    simp only [w]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    exact (pow_two S).symm
  have hid : ‖affineCoefficientSum G (1, 0)‖ ^ 2 = S ^ 2 := by
    rw [affineCoefficientSum_identity]
    have heq : (∑ r : (ZMod p)ˣ, conj (G r) * G r) = (S : ℂ) := by
      simp only [S, Complex.ofReal_sum, Complex.ofReal_pow, Complex.conj_mul']
    rw [heq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1, 0)), hid]
  have hrest : (∑ ab ∈ (Finset.univ : Finset ((ZMod p)ˣ × ZMod p)).erase (1, 0),
      ‖affineCoefficientSum G ab‖ ^ 2) ≤ 2 * S ^ 2 := by
    calc
      _ ≤ ∑ ab ∈ (Finset.univ : Finset ((ZMod p)ˣ × ZMod p)).erase (1, 0),
          2 * F ab := by
        apply Finset.sum_le_sum
        intro ab hab
        exact affineCoefficientSum_nonidentity_bound G ab (Finset.mem_erase.mp hab).1
      _ ≤ ∑ ab, 2 * F ab := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun ab _ _ => mul_nonneg (by norm_num) (hF ab))
      _ = 2 * S ^ 2 := by rw [← Finset.mul_sum, htotal]
  change _ ≤ 3 * S ^ 2
  linarith

/-- The coefficient normalization for the operator `T* T`. -/
noncomputable def affineCoefficient {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (ab : (ZMod p)ˣ × ZMod p) : ℂ :=
  affineCoefficientSum G ab / (((p : ℝ) ^ 2 : ℝ) : ℂ)

/-- Equation `tree-affine-coefficient-norm`, with the probability `L²` hypothesis. -/
theorem affineCoefficient_sq_sum_le {p : ℕ} [Fact p.Prime]
    (G : (ZMod p)ˣ → ℂ) (hG : (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ≤ (p : ℝ)) :
    (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficient G ab‖ ^ 2) ≤
      3 / (p : ℝ) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hG₀ : 0 ≤ ∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ = (∑ ab : (ZMod p)ˣ × ZMod p, ‖affineCoefficientSum G ab‖ ^ 2) /
        ((p : ℝ) ^ 2) ^ 2 := by
      simp only [affineCoefficient, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (p : ℝ)), div_pow,
        Finset.sum_div]
    _ ≤ (3 * (∑ r : (ZMod p)ˣ, ‖G r‖ ^ 2) ^ 2) / ((p : ℝ) ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right (affineCoefficientSum_sq_sum G) (sq_nonneg _)
    _ ≤ (3 * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hG₀ hp.le).mpr hG) (by norm_num)
    _ = 3 / (p : ℝ) ^ 2 := by field_simp [ne_of_gt hp]

end Ostmann

end OAI
