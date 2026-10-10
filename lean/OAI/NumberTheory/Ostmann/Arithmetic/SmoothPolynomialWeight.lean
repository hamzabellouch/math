import OAI.NumberTheory.Ostmann.Characters.PolynomialCellVariation
import OAI.NumberTheory.Ostmann.ZeroDensity.ReciprocalProgressionVariation

namespace OAI

/-! # Finite products of the smooth factors appearing in a history

Profiles are clipped to their prescribed argument ranges. This leaves their
values unchanged on the retained range and requires no continuity of the sharp
range indicator; those indicators are separate functions of the root cell.
-/

namespace Ostmann

open scoped BigOperators

structure ClippedPolynomialFactor where
  polynomial : Polynomial ℝ
  profile : ℝ → ℂ
  lo : ℝ
  hi : ℝ
  bound : ℝ
  lip : ℝ
  lo_le_hi : lo ≤ hi
  bound_nonneg : 0 ≤ bound
  lip_nonneg : 0 ≤ lip
  norm_le : ∀ x ∈ Set.Icc lo hi, ‖profile x‖ ≤ bound
  lipschitz : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
    ‖profile x - profile y‖ ≤ lip * |x - y|

noncomputable def ClippedPolynomialFactor.value (f : ClippedPolynomialFactor) (x : ℝ) : ℂ :=
  f.profile (clipRealInterval f.lo f.hi (f.polynomial.eval x))

theorem ClippedPolynomialFactor.value_of_mem (f : ClippedPolynomialFactor) (x : ℝ)
    (hx : f.polynomial.eval x ∈ Set.Icc f.lo f.hi) :
    f.value x = f.profile (f.polynomial.eval x) := by
  simp only [value, clipRealInterval, min_eq_right hx.2, max_eq_right hx.1]

theorem ClippedPolynomialFactor.norm_value (f : ClippedPolynomialFactor) (x : ℝ) :
    ‖f.value x‖ ≤ f.bound :=
  f.norm_le _ (clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi)

theorem ClippedPolynomialFactor.variation (f : ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ r, r ∈ f.polynomial.derivative.roots → r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1))) :
    discreteVariation (fun j => f.value (u j)) N ≤ f.bound + f.lip * (f.hi - f.lo) := by
  let v : ℕ → ℝ := fun j => clipRealInterval f.lo f.hi (f.polynomial.eval (u j))
  have hr (j : ℕ) (_hj : j ≤ N - 1) : v j ∈ Set.Icc f.lo f.hi :=
    clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi
  have hu' (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  change discreteVariation (fun j => f.profile (v j)) N ≤ _
  rcases polynomial_monotoneOn_of_root_cell f.polynomial S hroots hcode with hm | hm
  · apply discreteVariation_comp_monotoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))
  · apply discreteVariation_comp_antitoneOn f.profile v f.lo f.hi f.bound f.lip N
      f.lip_nonneg f.norm_le f.lipschitz hr
    intro j hj
    exact clipRealInterval_monotone f.lo f.hi
      (hm (hu' j hj.le) (hu' (j + 1) (by omega)) (hu (by omega)))

noncomputable def smoothPolynomialWeight {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (x : ℝ) : ℂ := ∏ i, (F i).value x

noncomputable def smoothPolynomialBudget {n : ℕ} (F : Fin n → ClippedPolynomialFactor) : ℝ :=
  ∏ i, (2 * (F i).bound + (F i).lip * ((F i).hi - (F i).lo))

theorem smoothPolynomialBudget_nonneg {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    0 ≤ smoothPolynomialBudget F := by
  apply Finset.prod_nonneg
  intro i _
  exact add_nonneg (mul_nonneg (by norm_num) (F i).bound_nonneg)
    (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))

theorem smoothPolynomialWeight_norm {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    ‖smoothPolynomialWeight F x‖ ≤ smoothPolynomialBudget F := by
  rw [smoothPolynomialWeight, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  apply ((F i).norm_value x).trans
  have h := mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi)
  linarith [(F i).bound_nonneg]

theorem smoothPolynomialWeight_variation {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1))) :
    discreteVariation (fun j => smoothPolynomialWeight F (u j)) N ≤ smoothPolynomialBudget F := by
  have hV (i : Fin n) : 0 ≤ (F i).bound + (F i).lip * ((F i).hi - (F i).lo) :=
    add_nonneg (F i).bound_nonneg
      (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))
  have ht := discreteVariation_prod n (fun i j => (F i).value (u j))
    (fun i => (F i).bound) (fun i => (F i).bound + (F i).lip * ((F i).hi - (F i).lo)) N
    (fun i => (F i).bound_nonneg) hV (fun i j => (F i).norm_value (u j))
    (fun i => (F i).variation S (hroots i) u hu N hcode)
  change discreteVariation (fun j => ∏ i, (F i).value (u j)) N ≤ _
  apply ht.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- This is the weight used after the long-prime prior is extended to integers. -/
theorem smoothPolynomial_reciprocal_variation {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (b d : ℝ) (hb : 0 < b) (hd : 0 ≤ d) (N : ℕ)
    (hcode : rootCellCode S b = rootCellCode S (b + d * ((N - 1 : ℕ) : ℝ))) :
    discreteVariation (fun j => Complex.ofReal ((b + d * j)⁻¹) *
      smoothPolynomialWeight F (b + d * j)) N ≤ 2 * b⁻¹ * smoothPolynomialBudget F := by
  have hu : Monotone (fun j : ℕ => b + d * j) := by
    intro i j hij
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hijR hd)
  have hc : rootCellCode S (b + d * (0 : ℕ)) = rootCellCode S (b + d * (N - 1 : ℕ)) := by
    simpa only [Nat.cast_zero, mul_zero, add_zero] using hcode
  exact reciprocal_progression_product_variation b d hb hd _ N
    (smoothPolynomialBudget F) (smoothPolynomialBudget F) le_rfl
    (fun j => smoothPolynomialWeight_norm F _) (smoothPolynomialWeight_variation F S hroots _ hu N hc)

end Ostmann

end OAI
