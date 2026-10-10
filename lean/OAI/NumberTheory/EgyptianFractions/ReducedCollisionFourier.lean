import OAI.NumberTheory.EgyptianFractions.RandomProductFourier
import OAI.NumberTheory.EgyptianFractions.ReducedCharacter

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The number of ordered pairs in an indexed list with the same residue.
The indices, rather than the image set, retain all multiplicities. -/
def indexedResidueCollisionCount {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) : ℕ :=
  (Finset.univ.filter (fun ij : ι × ι => f ij.1 = f ij.2)).card

/-- Squared fiber sizes exactly count pairs with equal images. -/
theorem sum_sq_residue_fiber_card {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) :
    (∑ x : ZMod q, ((Finset.univ.filter (fun i : ι => f i = x)).card : ℝ) ^ 2) =
      (indexedResidueCollisionCount f : ℝ) := by
  classical
  have hc : (∑ x : ZMod q,
      ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) ^ 2) =
      (indexedResidueCollisionCount f : ℂ) := by
    calc
      _ = ∑ i : ι, ((Finset.univ.filter (fun j : ι => f j = f i)).card : ℂ) := by
        simpa only [pow_two] using sum_fiber_card_mul f
          (fun x => ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ))
      _ = _ := by
        simp only [indexedResidueCollisionCount, Finset.card_filter, Nat.cast_sum,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [eq_comm]
  exact_mod_cast hc

/-- Exact regrouping of an indexed bilinear sum, with multiplicities. -/
theorem residue_fiber_double_sum {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) (g : ZMod q → ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q,
      ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) *
      ((Finset.univ.filter (fun i : ι => f i = y)).card : ℂ) * g x y) =
      ∑ i : ι, ∑ j : ι, g (f i) (f j) := by
  classical
  calc
    _ = ∑ x : ZMod q,
        ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) *
          (∑ y : ZMod q,
            ((Finset.univ.filter (fun i : ι => f i = y)).card : ℂ) * g x y) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i : ι, ∑ y : ZMod q,
        ((Finset.univ.filter (fun j : ι => f j = y)).card : ℂ) * g (f i) y :=
      sum_fiber_card_mul f _
    _ = _ := by simp_rw [sum_fiber_card_mul]

/-- The two-sided collision estimate at a primitive frequency. It uses the
actual squared mass, not a maximum-atom estimate. -/
theorem indexed_residue_bilinear_bound {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) (c : (ZMod q)ˣ) :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((c : ZMod q) * f i * f j)‖ ≤
      Real.sqrt (q : ℝ) * indexedResidueCollisionCount f := by
  classical
  let w : ZMod q → ℂ := fun x =>
    ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ)
  have hE : (∑ x : ZMod q, ‖w x‖ ^ 2) =
      (indexedResidueCollisionCount f : ℝ) := by
    simpa only [w, Complex.norm_natCast] using sum_sq_residue_fiber_card f
  have h := residue_bilinear_bound w w c
  have hs : (∑ x : ZMod q, ∑ y : ZMod q,
      w x * w y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ i : ι, ∑ j : ι, ZMod.stdAddChar ((c : ZMod q) * f i * f j) :=
    residue_fiber_double_sum f _
  rw [hs, hE] at h
  simpa only [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

/-- Nonprimitive frequencies reduce to their true conductor before applying
both collision factors. In particular there is no spurious ambient `sqrt(q)`
loss when the conductor is small. -/
theorem reduced_indexed_bilinear_bound {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (a q : ℕ) (hq : 0 < q)
    [NeZero q] [NeZero (q / a.gcd q)] :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((a * t i * t j : ℕ) : ZMod q)‖ ≤
      Real.sqrt ((q / a.gcd q : ℕ) : ℝ) *
        indexedResidueCollisionCount (fun i => (t i : ZMod (q / a.gcd q))) := by
  have h := indexed_residue_bilinear_bound
    (fun i => (t i : ZMod (q / a.gcd q))) (reducedFrequency a q hq)
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.mul_assoc, stdAddChar_reduced a q _ hq, Nat.cast_mul, mul_assoc]

/-- Normalized form of the conductor-sensitive collision estimate. It also
holds for an empty index type, under the usual zero-division convention. -/
theorem reduced_indexed_bilinear_average_bound {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (a q : ℕ) (hq : 0 < q)
    [NeZero q] [NeZero (q / a.gcd q)] :
    ‖(∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((a * t i * t j : ℕ) : ZMod q)) /
        (Fintype.card ι : ℂ) ^ 2‖ ≤
      Real.sqrt ((q / a.gcd q : ℕ) : ℝ) *
        (indexedResidueCollisionCount (fun i => (t i : ZMod (q / a.gcd q))) : ℝ) /
          (Fintype.card ι : ℝ) ^ 2 := by
  rw [norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (reduced_indexed_bilinear_bound t a q hq)
    (sq_nonneg _)

end Problem337

end

end OAI
