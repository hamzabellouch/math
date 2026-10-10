import OAI.Algebra.DepthFive.ExponentCardinality

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- A weak composition indexed by a finite variable set. -/
abbrev Composition (σ : Type*) [Fintype σ] (a : ℕ) :=
  {d : σ → ℕ // ∑ x, d x = a}

/-- The exponent index set for the source of the mixed operator. -/
abbrev Index {σ : Type*} (isV : σ → Bool) (a b : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight isV) d = (a, b)}

/-- Summing a separated function over bihomogeneous exponent vectors factors
into the two weak-composition sums. This is the independence of the two
occupation groups, not independence of coordinates within either group. -/
theorem sum_split {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) =
      (∑' v : Composition {x // isV x = true} a, f v.val) *
        (∑' u : Composition {x // ¬ isV x = true} b, g u.val) := by
  classical
  let : Fintype (Composition {x // isV x = true} a) :=
    Fintype.ofEquiv (Sym {x // isV x = true} a)
      (Sym.equivNatSumOfFintype _ _)
  let : Fintype (Composition {x // ¬ isV x = true} b) :=
    Fintype.ofEquiv (Sym {x // ¬ isV x = true} b)
      (Sym.equivNatSumOfFintype _ _)
  calc
    _ = ∑' z : Composition {x // isV x = true} a ×
        Composition {x // ¬ isV x = true} b, f z.1.val * g z.2.val :=
      (bidegreeExponentsEquiv isV a b).tsum_eq (fun z => f z.1.val * g z.2.val)
    _ = _ := by
      simp only [tsum_fintype, Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum
        (fun v : Composition {x // isV x = true} a => f v.val)
        (fun u : Composition {x // ¬ isV x = true} b => g u.val)).symm

/-- The normalized form of `sum_split`: the uniform domain occupation average
is the product of the two uniform weak-composition averages. Empty index sets
are handled by the usual convention that division by zero is zero. -/
theorem average_split {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Nat.card (Index isV a b) : ℝ) =
      ((∑' v : Composition {x // isV x = true} a, f v.val) /
        (Nat.card (Composition {x // isV x = true} a) : ℝ)) *
      ((∑' u : Composition {x // ¬ isV x = true} b, g u.val) /
        (Nat.card (Composition {x // ¬ isV x = true} b) : ℝ)) := by
  rw [sum_split, Nat.card_congr (bidegreeExponentsEquiv isV a b),
    Nat.card_prod, Nat.cast_mul, div_mul_div_comm]

/-- Finite-sum version, compatible with any chosen enumerations of the three
finite index types (in particular with matrix bases). -/
theorem sum_split_fintype {σ : Type*} [Fintype σ] (isV : σ → Bool) (a b : ℕ)
    [Fintype (Index isV a b)]
    [Fintype (Composition {x // isV x = true} a)]
    [Fintype (Composition {x // ¬ isV x = true} b)]
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑ d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) =
      (∑ v : Composition {x // isV x = true} a, f v.val) *
        (∑ u : Composition {x // ¬ isV x = true} b, g u.val) := by
  simpa only [tsum_fintype] using sum_split isV a b f g

/-- The average identity with the exact stars-and-bars dimension factors. -/
theorem average_split_multichoose {σ : Type*} [Fintype σ]
    (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (((Fintype.card {x // isV x = true}).multichoose a : ℝ) *
        ((Fintype.card {x // ¬ isV x = true}).multichoose b : ℝ)) =
      ((∑' v : Composition {x // isV x = true} a, f v.val) /
        ((Fintype.card {x // isV x = true}).multichoose a : ℝ)) *
      ((∑' u : Composition {x // ¬ isV x = true} b, g u.val) /
        ((Fintype.card {x // ¬ isV x = true}).multichoose b : ℝ)) := by
  simpa only [Index, Composition, card_bidegree_exponents,
    card_homogeneous_functions, Nat.cast_mul] using average_split isV a b f g

end Problem335.BidegreeAverages

end

end OAI
