import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPrimeComparison

namespace OAI

/-! # Smooth variation when roots are retained at the cell endpoints -/

namespace Ostmann
open scoped BigOperators

theorem polynomial_monotoneOn_no_roots (P : Polynomial ℝ) (a b : ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∉ Set.Ioo a b) :
    MonotoneOn P.eval (Set.Icc a b) ∨ AntitoneOn P.eval (Set.Icc a b) := by
  by_cases hd : P.derivative = 0
  · left
    have hp := Polynomial.eq_C_of_derivative_eq_zero hd
    intro x hx y hy hxy
    have hv (t : ℝ) : P.eval t = P.coeff 0 := by
      have hh := congrArg (fun Q : Polynomial ℝ => Q.eval t) hp
      simpa only [Polynomial.eval_C] using hh
    change P.eval x ≤ P.eval y
    rw [hv x, hv y]
  · have hn : ∀ x ∈ Set.Ioo a b, P.derivative.eval x ≠ 0 := by
      intro x hx hz
      exact hroots x ((Polynomial.mem_roots hd).mpr hz) hx
    rcases continuous_sign_on_interval P.derivative.eval a b
        P.derivative.continuous.continuousOn hn with hpos | hneg
    · left
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hpos x hx
    · right
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hneg x hx

theorem ClippedPolynomialFactor.variation_no_roots (f : ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ r ∈ f.polynomial.derivative.roots, r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => f.value (u j)) N ≤ f.bound + f.lip * (f.hi - f.lo) := by
  let v : ℕ → ℝ := fun j => clipRealInterval f.lo f.hi (f.polynomial.eval (u j))
  have hr (j : ℕ) (_hj : j ≤ N - 1) : v j ∈ Set.Icc f.lo f.hi :=
    clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi
  have hu' (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  change discreteVariation (fun j => f.profile (v j)) N ≤ _
  rcases polynomial_monotoneOn_no_roots f.polynomial (u 0) (u (N - 1)) hroots with hm | hm
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

theorem smoothPolynomialWeight_variation_no_roots {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots →
      r ∉ Set.Ioo (u 0) (u (N - 1))) :
    discreteVariation (fun j => smoothPolynomialWeight F (u j)) N ≤ smoothPolynomialBudget F := by
  have hV (i : Fin n) : 0 ≤ (F i).bound + (F i).lip * ((F i).hi - (F i).lo) :=
    add_nonneg (F i).bound_nonneg
      (mul_nonneg (F i).lip_nonneg (sub_nonneg.mpr (F i).lo_le_hi))
  have ht := discreteVariation_prod n (fun i j => (F i).value (u j))
    (fun i => (F i).bound) (fun i => (F i).bound + (F i).lip * ((F i).hi - (F i).lo)) N
    (fun i => (F i).bound_nonneg) hV (fun i j => (F i).norm_value (u j))
    (fun i => (F i).variation_no_roots u hu N (hroots i))
  change discreteVariation (fun j => ∏ i, (F i).value (u j)) N ≤ _
  apply ht.trans_eq
  apply Finset.prod_congr rfl
  intro i _
  ring

end Ostmann

end OAI
