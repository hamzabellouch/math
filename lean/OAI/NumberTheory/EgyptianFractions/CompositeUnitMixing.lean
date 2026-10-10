import OAI.NumberTheory.EgyptianFractions.BilinearFourier

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The sum of unit translates has squared energy at most the number of
translates squared times the original energy. This needs no primality and
no positivity hypothesis on the original real-valued function. -/
theorem sum_sq_unit_mixing {q : ℕ} [NeZero q]
    {J : Type*} [Fintype J] (c : J → (ZMod q)ˣ) (w : ZMod q → ℝ) :
    (∑ x : ZMod q, (∑ j : J, w ((c j : ZMod q) * x)) ^ 2) ≤
      (Fintype.card J : ℝ) ^ 2 * ∑ x : ZMod q, w x ^ 2 := by
  classical
  have hpoint (x : ZMod q) :
      (∑ j : J, w ((c j : ZMod q) * x)) ^ 2 ≤
        (Fintype.card J : ℝ) * ∑ j : J, w ((c j : ZMod q) * x) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset J) (fun _ => (1 : ℝ))
        (fun j => w ((c j : ZMod q) * x))
  calc
    _ ≤ ∑ x : ZMod q, (Fintype.card J : ℝ) *
        ∑ j : J, w ((c j : ZMod q) * x) ^ 2 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (Fintype.card J : ℝ) * ∑ j : J,
        ∑ x : ZMod q, w ((c j : ZMod q) * x) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (Fintype.card J : ℝ) ^ 2 * ∑ x : ZMod q, w x ^ 2 := by
      have hperm (j : J) :
          (∑ x : ZMod q, w ((c j : ZMod q) * x) ^ 2) =
            ∑ x : ZMod q, w x ^ 2 :=
        Equiv.sum_comp (c j).mulLeft (fun x => w x ^ 2)
      simp_rw [hperm]
      simp [pow_two, mul_assoc]

/-- Averaging arbitrary unit permutations cannot increase squared energy.
In particular, adjoining independent prime choices coprime to a modulus
preserves any known upper bound for the projected divisor distribution. -/
theorem average_sq_unit_mixing {q : ℕ} [NeZero q]
    {J : Type*} [Fintype J] (c : J → (ZMod q)ˣ) (w : ZMod q → ℝ) :
    (∑ x : ZMod q,
      ((∑ j : J, w ((c j : ZMod q) * x)) / (Fintype.card J : ℝ)) ^ 2) ≤
        ∑ x : ZMod q, w x ^ 2 := by
  classical
  by_cases hJ : Fintype.card J = 0
  · simp [hJ, Finset.sum_nonneg (fun x _ => sq_nonneg (w x))]
  · have hJpos : (0 : ℝ) < Fintype.card J := by exact_mod_cast Nat.pos_of_ne_zero hJ
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ (pow_pos hJpos 2)).mpr
    simpa only [mul_comm] using sum_sq_unit_mixing c w

/-- Multiplying an indexed sample by independent units transforms its fibers
by averaging inverse unit translations. Multiplicities are retained. -/
theorem unit_mixed_fiber_count {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) (x : ZMod q) :
    (Finset.univ.filter (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card =
      ∑ j : J, (Finset.univ.filter
        (fun i : I => f i = ((c j)⁻¹ : (ZMod q)ˣ) * x)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [← (c j).eq_inv_mul_iff_mul_eq]

/-- The exact normalized finite-sample mass identity used in unit mixing.
The formula is valid even for an empty index type, using totalized division. -/
theorem unit_mixed_fiber_mass {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) (x : ZMod q) :
    ((Finset.univ.filter (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card : ℝ) /
        (Fintype.card (I × J) : ℝ) =
      (∑ j : J,
        ((Finset.univ.filter (fun i : I => f i = ((c j)⁻¹ : (ZMod q)ˣ) * x)).card : ℝ) /
          (Fintype.card I : ℝ)) / (Fintype.card J : ℝ) := by
  classical
  rw [unit_mixed_fiber_count, Nat.cast_sum, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]

/-- Adjoining an independent list of units cannot increase the normalized
collision energy of a finite indexed residue sample. This is the precise
nesting principle for divisor lists at moduli coprime to the added primes. -/
theorem indexed_energy_unit_mixing {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) :
    (∑ x : ZMod q,
      (((Finset.univ.filter
        (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card : ℝ) /
          (Fintype.card (I × J) : ℝ)) ^ 2) ≤
      ∑ x : ZMod q,
        (((Finset.univ.filter (fun i : I => f i = x)).card : ℝ) /
          (Fintype.card I : ℝ)) ^ 2 := by
  classical
  simp_rw [unit_mixed_fiber_mass]
  exact average_sq_unit_mixing (fun j => (c j)⁻¹)
    (fun x => ((Finset.univ.filter (fun i : I => f i = x)).card : ℝ) /
      (Fintype.card I : ℝ))

end Problem337

end

end OAI
