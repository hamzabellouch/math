import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

/-!
# Equal-mass two-point Gauss rule

The tensor product of this degree-three rule uses eight equal masses in each
three-dimensional cell. Exact moment identities and fourth-derivative estimates
control its error.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace ContinuumCoulomb

def gaussAbscissa : ℝ := (Real.sqrt 3)⁻¹

def gaussTwoPoint (f : ℝ → ℝ) : ℝ := f (-gaussAbscissa) + f gaussAbscissa

theorem gaussAbscissa_pos : 0 < gaussAbscissa := by
  unfold gaussAbscissa
  positivity

theorem gaussAbscissa_sq : gaussAbscissa ^ 2 = (1 / 3 : ℝ) := by
  rw [gaussAbscissa, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- Exactness for all four monomial moments needed in each coordinate. -/
theorem gaussTwoPoint_moment (k : ℕ) (hk : k ≤ 3) :
    gaussTwoPoint (fun x => x ^ k) = ∫ x : ℝ in (-1)..1, x ^ k := by
  interval_cases k
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow]
  · norm_num [gaussTwoPoint, integral_pow, gaussAbscissa_sq]
  · norm_num [gaussTwoPoint, integral_pow]
    ring

/-- Equal-weight quadrature integrates every cubic exactly. -/
theorem gaussTwoPoint_cubic (coefficient : Fin 4 → ℝ) :
    gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
      ∫ x : ℝ in (-1)..1, ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
  have hsum :
      gaussTwoPoint (fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)) =
        ∑ k : Fin 4, coefficient k * gaussTwoPoint (fun x => x ^ (k : ℕ)) := by
    unfold gaussTwoPoint
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [gaussTwoPoint_moment k (by omega), intervalIntegral.integral_const_mul]
  · intro k _
    exact (continuous_const.mul (continuous_id.pow (k : ℕ))).intervalIntegrable _ _

/-- In the centered cell of side `h`, the distinct nodes lie strictly inside. -/
theorem gauss_cell_nodes {h : ℝ} (hh : 0 < h) :
    -h / 2 < -(h / 2) * gaussAbscissa ∧
    -(h / 2) * gaussAbscissa < (h / 2) * gaussAbscissa ∧
    (h / 2) * gaussAbscissa < h / 2 := by
  have hp := gaussAbscissa_pos
  have hs := gaussAbscissa_sq
  have hlt : gaussAbscissa < 1 := by nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The eight masses sum to the uniform charge of a cell. -/
theorem eight_node_mass (rho h : ℝ) :
    (8 : ℝ) * (rho * h ^ 3 / 8) = rho * h ^ 3 := by ring

/-- The manuscript's scale choice makes each mass exactly `1 / λ`. -/
theorem unit_node_mass {rho k : ℝ} (hrho : 0 < rho) (hk : 0 < k) :
    rho * (1 / k) ^ 3 / 8 = 1 / (8 * k ^ 3 / rho) := by
  field_simp

/-- The two normalized abscissae, indexed for the tensor-product rule. -/
def gaussNode (b : Fin 2) : ℝ := if b = 0 then -gaussAbscissa else gaussAbscissa

/-- The three-dimensional rule is exact for each needed tensor monomial. -/
theorem gaussTensor3_moment (degree : Fin 3 → ℕ) (hdegree : ∀ i, degree i ≤ 3) :
    (∑ node : Fin 3 → Fin 2, ∏ i : Fin 3, gaussNode (node i) ^ degree i) =
      ∏ i : Fin 3, ∫ x : ℝ in (-1)..1, x ^ degree i := by
  rw [← Fintype.prod_sum (fun (i : Fin 3) (b : Fin 2) => gaussNode b ^ degree i)]
  apply Finset.prod_congr rfl
  intro i _
  have h : (∑ b : Fin 2, gaussNode b ^ degree i) =
      gaussTwoPoint (fun x => x ^ degree i) := by
    simp [gaussNode, gaussTwoPoint, Fin.sum_univ_succ]
  rw [h, gaussTwoPoint_moment (degree i) (hdegree i)]

/-- Exactly eight equal masses are used in a three-dimensional cell. -/
theorem gaussTensor3_mass (rho h : ℝ) :
    (∑ _node : Fin 3 → Fin 2, rho * h ^ 3 / 8) = rho * h ^ 3 := by
  simp
  ring

/-- Uniform cubic approximation controls the quadrature and integral errors
separately, using the positivity and total mass of the rule. -/
theorem gaussTwoPoint_remainder_bound
    (f : ℝ → ℝ) (coefficient : Fin 4 → ℝ) {epsilon : ℝ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ epsilon) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ 4 * epsilon := by
  let p : ℝ → ℝ := fun x => ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)
  have hp : Continuous p := by unfold p; fun_prop
  have hg0 := gaussAbscissa_pos.le
  have hg1 : gaussAbscissa ≤ 1 := by nlinarith [gaussAbscissa_sq]
  have hleft := happrox (-gaussAbscissa) ⟨by linarith, by linarith⟩
  have hright := happrox gaussAbscissa ⟨by linarith, hg1⟩
  have hint : |∫ x : ℝ in (-1)..1, (f x - p x)| ≤ 2 * epsilon := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => f x - p x) (a := -1) (b := 1) (C := epsilon) ?_
    · norm_num [Real.norm_eq_abs] at h
      simpa only [mul_comm] using h
    · intro x hx
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs, p] using happrox x ⟨hx'.1.le, hx'.2⟩
  have hfi : IntervalIntegrable f volume (-1) 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hf
  have hpi : IntervalIntegrable p volume (-1) 1 := hp.intervalIntegrable _ _
  have heq : gaussTwoPoint f - (∫ x : ℝ in (-1)..1, f x) =
      (f (-gaussAbscissa) - p (-gaussAbscissa)) +
        (f gaussAbscissa - p gaussAbscissa) -
          (∫ x : ℝ in (-1)..1, f x - p x) := by
    rw [intervalIntegral.integral_sub hfi hpi]
    have h := gaussTwoPoint_cubic coefficient
    change p (-gaussAbscissa) + p gaussAbscissa = ∫ x : ℝ in (-1)..1, p x at h
    unfold gaussTwoPoint
    linarith
  rw [heq]
  calc
    _ ≤ |f (-gaussAbscissa) - p (-gaussAbscissa)| +
        |f gaussAbscissa - p gaussAbscissa| + |∫ x : ℝ in (-1)..1, f x - p x| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 4 * epsilon := by dsimp [p] at *; linarith

/-- A genuine fourth-derivative error bound for the normalized cell. The
coarse constant suffices for the manuscript's polynomial error budgets. -/
theorem gaussTwoPoint_C4_error (f : ℝ → ℝ) {C : ℝ} (hCnonneg : 0 ≤ C)
    (hf : ContDiffOn ℝ 4 f (Set.Icc (-1) 1))
    (hC : ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 f (Set.Icc (-1) 1) x‖ ≤ C) :
    |gaussTwoPoint f - ∫ x : ℝ in (-1)..1, f x| ≤ (32 / 3 : ℝ) * C := by
  let d : Fin 4 → ℝ := fun k => taylorCoeffWithin f (k : ℕ) (Set.Icc (-1) 1) (-1)
  let coefficient : Fin 4 → ℝ :=
    ![d 0 + d 1 + d 2 + d 3, d 1 + 2 * d 2 + 3 * d 3, d 2 + 3 * d 3, d 3]
  have htaylor (x : ℝ) :
      taylorWithinEval f 3 (Set.Icc (-1) 1) (-1) x =
        ∑ k : Fin 4, coefficient k * x ^ (k : ℕ) := by
    rw [taylor_within_apply]
    norm_num [coefficient, d, taylorCoeffWithin, Fin.sum_univ_succ,
      Finset.sum_range_succ, smul_eq_mul]
    ring
  have happrox : ∀ x ∈ Set.Icc (-1) 1,
      |f x - ∑ k : Fin 4, coefficient k * x ^ (k : ℕ)| ≤ (8 / 3 : ℝ) * C := by
    intro x hx
    have h := taylor_mean_remainder_bound (n := 3) (by norm_num : (-1 : ℝ) ≤ 1)
      hf hx hC
    rw [htaylor x] at h
    norm_num [Real.norm_eq_abs, sub_neg_eq_add] at h
    have hp : (x + 1) ^ 4 ≤ (16 : ℝ) := by
      calc
        (x + 1) ^ 4 ≤ (2 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 4
        _ = 16 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hp hCnonneg
    nlinarith
  have h := gaussTwoPoint_remainder_bound f coefficient hf.continuousOn happrox
  convert h using 1
  ring

/-- The equal-weight rule on an actual interval, with its physical weights. -/
def gaussCell (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (b - a) / 2 * gaussTwoPoint (fun t => f ((a + b) / 2 + (b - a) / 2 * t))

/-- Local fourth-derivative control gives the fifth-power cell error needed
when the eight-node tensor rule is summed over a fine mesh. No smoothness
outside the cell is assumed, which matters for the Coulomb kernel. -/
theorem gaussCell_C4_error (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    {C : ℝ} (hCnonneg : 0 ≤ C) (hf : ContDiffOn ℝ 4 f (Set.Icc a b))
    (hC : ∀ x ∈ Set.Icc a b, ‖iteratedDerivWithin 4 f (Set.Icc a b) x‖ ≤ C) :
    |gaussCell a b f - ∫ x : ℝ in a..b, f x| ≤ C * (b - a) ^ 5 / 3 := by
  let c : ℝ := (a + b) / 2
  let d : ℝ := (b - a) / 2
  let g : ℝ → ℝ := fun t => f (c + d * t)
  let v : Fin 4 → ℝ := fun k => taylorCoeffWithin f (k : ℕ) (Set.Icc a b) a
  let coefficient : Fin 4 → ℝ :=
    ![v 0 + v 1 * d + v 2 * d ^ 2 + v 3 * d ^ 3,
      v 1 * d + 2 * v 2 * d ^ 2 + 3 * v 3 * d ^ 3,
      v 2 * d ^ 2 + 3 * v 3 * d ^ 3, v 3 * d ^ 3]
  have hd : 0 < d := by dsimp [d]; linarith
  have hmap : Set.MapsTo (fun t => c + d * t) (Set.Icc (-1) 1) (Set.Icc a b) := by
    intro t ht
    dsimp [c, d]
    constructor <;> nlinarith [ht.1, ht.2]
  have htaylor (t : ℝ) : taylorWithinEval f 3 (Set.Icc a b) a (c + d * t) =
      ∑ k : Fin 4, coefficient k * t ^ (k : ℕ) := by
    rw [taylor_within_apply]
    norm_num [coefficient, v, taylorCoeffWithin, Fin.sum_univ_succ,
      Finset.sum_range_succ, smul_eq_mul]
    dsimp [c, d]
    ring
  have happrox : ∀ t ∈ Set.Icc (-1) 1,
      |g t - ∑ k : Fin 4, coefficient k * t ^ (k : ℕ)| ≤ C * (b - a) ^ 4 / 6 := by
    intro t ht
    have hx := hmap ht
    have h := taylor_mean_remainder_bound (n := 3) hab.le hf hx hC
    rw [htaylor t] at h
    norm_num [Real.norm_eq_abs] at h
    have hp : (c + d * t - a) ^ 4 ≤ (b - a) ^ 4 :=
      pow_le_pow_left₀ (by linarith [hx.1]) (by linarith [hx.2]) 4
    exact h.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp hCnonneg) (by norm_num))
  have hg : ContinuousOn g (Set.Icc (-1) 1) :=
    hf.continuousOn.comp (by fun_prop) hmap
  have h := mul_le_mul_of_nonneg_left
    (gaussTwoPoint_remainder_bound g coefficient hg happrox) hd.le
  have hint : d * (∫ t : ℝ in (-1)..1, g t) = ∫ x : ℝ in a..b, f x := by
    have hsub := intervalIntegral.smul_integral_comp_add_mul
      (f := f) (a := (-1 : ℝ)) (b := 1) d c
    have hl : c + d * (-1) = a := by dsimp [c, d]; ring
    have hr : c + d * 1 = b := by dsimp [c, d]; ring
    simpa only [smul_eq_mul, hl, hr, g] using hsub
  have heq : |gaussCell a b f - ∫ x : ℝ in a..b, f x| =
      d * |gaussTwoPoint g - ∫ t : ℝ in (-1)..1, g t| := by
    change |d * gaussTwoPoint g - ∫ x : ℝ in a..b, f x| = _
    rw [← hint, ← mul_sub, abs_mul, abs_of_pos hd]
  rw [heq]
  convert h using 1
  dsimp [d]
  ring

end ContinuumCoulomb

end

end OAI
