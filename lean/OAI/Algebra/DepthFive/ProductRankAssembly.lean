import OAI.Algebra.DepthFive.Bidegree
import OAI.Algebra.DepthFive.DegreeDiscrepancy
import OAI.Algebra.DepthFive.RankMeasure

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace ProductRankAssembly

variable {σ K ι : Type*} [CommSemiring K] [Fintype ι] [DecidableEq ι]

/-- The rank subadditivity step, stated for a real-valued polynomial measure. -/
theorem measure_sum_le (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    {α : Type*} (s : Finset α) (f : α → MvPolynomial σ K) :
    R (∑ a ∈ s, f a) ≤ ∑ a ∈ s, R (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hadd _ _).trans (add_le_add le_rfl ih)

/-- A product's fixed bidegree has rank at most the sum over exactly those
assignments with matching total degree. -/
theorem measure_component_product_le_sum
    (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    (side : σ → Bool) (p : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ) :
    R (Bidegree.component side k (∏ j, p j)) ≤
      ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), R (∏ j, Bidegree.component side (i j) (p j)) := by
  classical
  have hdecomp : Bidegree.component side k (∏ j, p j) =
      ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), ∏ j, Bidegree.component side (i j) (p j) := by
    rw [Bidegree.component_prod side p e hp k, Finset.sum_filter]
  rw [hdecomp]
  exact measure_sum_le R hzero hadd _ _

/-- The constrained bidegree decomposition and the nonnegative assignment sum
turn per-assignment weight bounds into the product-rank estimate. -/
theorem measure_component_product_le_degreeWeight
    (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    (side : σ → Bool) (p : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ)
    (C q lam : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hterm : ∀ i : ι → ℕ, (∀ j, i j ≤ e j) → (∑ j, i j) = k →
      R (∏ j, Bidegree.component side (i j) (p j)) ≤
        C * ∏ j, q ^ |(i j : ℝ) - lam * e j|) :
    R (Bidegree.component side k (∏ j, p j)) ≤
      C * ∏ j, degreeWeight q lam (e j) := by
  classical
  calc
    _ ≤ ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), R (∏ j, Bidegree.component side (i j) (p j)) :=
      measure_component_product_le_sum R hzero hadd side p e hp k
    _ ≤ ∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), C * ∏ j, q ^ |(i j : ℝ) - lam * e j| := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi, hsum⟩ := Finset.mem_filter.mp hi
      apply hterm i _ hsum
      intro j
      have hj := (Fintype.mem_piFinset.mp hi) j
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    _ = C * (∑ i ∈ (Fintype.piFinset (fun j => Finset.range (e j + 1))).filter
        (fun i => ∑ j, i j = k), ∏ j, q ^ |(i j : ℝ) - lam * e j|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∏ j, degreeWeight q lam (e j) :=
      mul_le_mul_of_nonneg_left (bidegree_weight_sum_le e k q lam hq) hC

/-- The full algebraic product-rank assembly: the remaining input is
the geometric bound through the selected intermediate homogeneous space. -/
theorem measure_component_product_le_of_intermediate_bounds
    (R : MvPolynomial σ K → ℝ)
    (hzero : R 0 = 0) (hadd : ∀ p q, R (p + q) ≤ R p + R q)
    (side : σ → Bool) (p : ι → MvPolynomial σ K) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ)
    (D alpha rho lam : ℝ) (hD : 0 ≤ D) (halpha : 0 < alpha)
    (hslope : (1 + rho) * lam = rho)
    (hbalance : lam * (∑ j, (e j : ℝ)) = k)
    (hterm : ∀ i : ι → ℕ, (∀ j, i j ≤ e j) → (∑ j, i j) = k →
      R (∏ j, Bidegree.component side (i j) (p j)) ≤
        2 * D * alpha ^ ((∑ j ∈ Finset.univ.filter
          (fun j => 0 < (i j : ℝ) - lam * e j), (i j : ℝ)) -
          rho * (∑ j ∈ Finset.univ.filter
          (fun j => 0 < (i j : ℝ) - lam * e j), ((e j : ℝ) - i j)))) :
    R (Bidegree.component side k (∏ j, p j)) ≤
      2 * D * ∏ j, degreeWeight (alpha ^ ((1 + rho) / 2)) lam (e j) := by
  apply measure_component_product_le_degreeWeight R hzero hadd side p e hp k
    (2 * D) (alpha ^ ((1 + rho) / 2)) lam (by positivity) (by positivity)
  intro i hi hsum
  have hsumR : (∑ j, (i j : ℝ)) = k := by exact_mod_cast hsum
  have hdelta : (∑ j, ((i j : ℝ) - lam * e j)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumR, hbalance, sub_self]
  have hpow := positive_bidegree_rpow Finset.univ
    (fun j => (e j : ℝ)) (fun j => (i j : ℝ)) rho lam alpha halpha hslope hdelta
  simpa only [hpow] using hterm i hi hsum

section LinearFamilies

variable {F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W]

/-- Specialization to the actual finite-dimensional rank measure of a linear
operator family, without any extra subadditivity hypotheses. -/
theorem rank_component_product_le_of_intermediate_bounds
    (A : MvPolynomial σ F →ₗ[F] (V →ₗ[F] W))
    (side : σ → Bool) (p : ι → MvPolynomial σ F) (e : ι → ℕ)
    (hp : ∀ j, (p j).IsHomogeneous (e j)) (k : ℕ)
    (D alpha rho lam : ℝ) (hD : 0 ≤ D) (halpha : 0 < alpha)
    (hslope : (1 + rho) * lam = rho)
    (hbalance : lam * (∑ j, (e j : ℝ)) = k)
    (hterm : ∀ i : ι → ℕ, (∀ j, i j ≤ e j) → (∑ j, i j) = k →
      (RankMeasure.measure A (∏ j, Bidegree.component side (i j) (p j)) : ℝ) ≤
        2 * D * alpha ^ ((∑ j ∈ Finset.univ.filter
          (fun j => 0 < (i j : ℝ) - lam * e j), (i j : ℝ)) -
          rho * (∑ j ∈ Finset.univ.filter
          (fun j => 0 < (i j : ℝ) - lam * e j), ((e j : ℝ) - i j)))) :
    (RankMeasure.measure A (Bidegree.component side k (∏ j, p j)) : ℝ) ≤
      2 * D * ∏ j, degreeWeight (alpha ^ ((1 + rho) / 2)) lam (e j) := by
  apply measure_component_product_le_of_intermediate_bounds
    (fun p => (RankMeasure.measure A p : ℝ)) (by simp) _
    side p e hp k D alpha rho lam hD halpha hslope hbalance hterm
  intro p q
  exact_mod_cast RankMeasure.measure_add_le A p q

end LinearFamilies

end ProductRankAssembly
end Problem335

end

end OAI
