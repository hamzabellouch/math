import OAI.NumberTheory.EgyptianFractions.CompositeConductorBudget
import OAI.NumberTheory.EgyptianFractions.ReducedCollisionFourier

namespace OAI
/-!
# Eight products from a subuniform conductor collision bound

A collision exponent of `7/8`, unlike exact equidistribution, is compatible
with the rough-modulus exceptional-set construction. Eight products then
produce a cubic conductor loss, controlled by the existing uniform `3/4`
conductor budget. The index type retains all sample multiplicities.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- A pointwise eighth-moment bound suffices for eight indexed products with
any prescribed sum. This formulation avoids fractional powers in consumers. -/
theorem eight_products_of_conductor_power_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ZMod q)
    (hchar : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ i : ι, ∑ j : ι, ZMod.stdAddChar (v i * v j * r)‖ ^ 8 ≤
        (Fintype.card ι : ℝ) ^ 16 / (addOrderOf r : ℝ) ^ 3)
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι, ∑ i, v (a i) * v (b i) = target := by
  classical
  let f : ι × ι → ZMod q := fun ij => v ij.1 * v ij.2
  let B : ZMod q → ℝ := fun r => ‖∑ ij : ι × ι, ZMod.stdAddChar (f ij * r)‖
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbudget : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ 8) <
      (Fintype.card (ι × ι) : ℝ) ^ 8 := by
    calc
      _ ≤ ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          (Fintype.card ι : ℝ) ^ 16 / (addOrderOf r : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro r hr
        simpa only [B, f, Fintype.sum_prod_type] using hchar r (Finset.mem_erase.mp hr).1
      _ = (Fintype.card ι : ℝ) ^ 16 *
          ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
            (1 : ℝ) / (addOrderOf r : ℝ) ^ 3 := by
        simp only [Finset.mul_sum, mul_one_div]
      _ ≤ (Fintype.card ι : ℝ) ^ 16 * (3 / 4) :=
        mul_le_mul_of_nonneg_left (conductor_cube_sum_le q) (by positivity)
      _ < (Fintype.card ι : ℝ) ^ 16 := by nlinarith [pow_pos hcard 16]
      _ = _ := by simp only [Fintype.card_prod, Nat.cast_mul]; ring
  obtain ⟨w, hw⟩ := exists_sum_of_character_bounds f 8 target B
    (fun _ _ => le_rfl) hbudget
  exact ⟨fun i => (w i).1, fun i => (w i).2, hw⟩

/-- Ordered residue-collision pairs, expressed with natural remainders so
no typeclass proof is part of the collision function's data. -/
def remainderCollisionCount {ι : Type*} [Fintype ι] (t : ι → ℕ) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun ij : ι × ι => t ij.1 % d = t ij.2 % d)).card

lemma remainderCollisionCount_eq_cast {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (d : ℕ) [NeZero d] :
    remainderCollisionCount t d =
      indexedResidueCollisionCount (fun i => (t i : ZMod d)) := by
  classical
  simp only [remainderCollisionCount, indexedResidueCollisionCount,
    ZMod.natCast_eq_natCast_iff']

/-- Conductor-sensitive bilinear estimate in the natural-remainder convention. -/
lemma bilinear_le_sqrt_order_mul_collisions
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (r : ZMod q) :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((t i : ZMod q) * (t j : ZMod q) * r)‖ ≤
        Real.sqrt (addOrderOf r : ℝ) * remainderCollisionCount t (addOrderOf r) := by
  have ho := order_eq_reduced_modulus r
  have hdpos : 0 < q / r.val.gcd q := by rw [← ho]; exact addOrderOf_pos r
  let : NeZero (q / r.val.gcd q) := ⟨Nat.ne_of_gt hdpos⟩
  have hb := reduced_indexed_bilinear_bound t r.val q (NeZero.pos q)
  rw [← remainderCollisionCount_eq_cast, ← ho] at hb
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- A purely polynomial collision hypothesis at every nontrivial divisor of
`q` gives eight products with every prescribed residue. The hypothesis is the
power-eight form of collision density at most `d^(-7/8)`. -/
theorem eight_products_of_collision_power_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t : ι → ℕ)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (remainderCollisionCount t d : ℝ) ^ 8 * (d : ℝ) ^ 7 ≤
        (Fintype.card ι : ℝ) ^ 16)
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι,
      ∑ i, (t (a i) : ZMod q) * (t (b i) : ZMod q) = target := by
  apply eight_products_of_conductor_power_bound (fun i => (t i : ZMod q)) _ target
  intro r hr
  have hdpos : 0 < addOrderOf r := addOrderOf_pos r
  have hd2 : 2 ≤ addOrderOf r := by
    have hne : addOrderOf r ≠ 1 := by
      intro h
      exact hr (AddMonoid.addOrderOf_eq_one_iff.mp h)
    omega
  have hdq : addOrderOf r ∣ q := by simpa using addOrderOf_dvd_card (x := r)
  have hbound := hcollision (addOrderOf r) hd2 hdq
  have hdR : (0 : ℝ) < addOrderOf r := by exact_mod_cast hdpos
  have hsqrt : Real.sqrt (addOrderOf r : ℝ) ^ 8 = (addOrderOf r : ℝ) ^ 4 := by
    calc
      _ = (Real.sqrt (addOrderOf r : ℝ) ^ 2) ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hdR.le]
  calc
    _ ≤ (Real.sqrt (addOrderOf r : ℝ) *
        remainderCollisionCount t (addOrderOf r)) ^ 8 :=
      pow_le_pow_left₀ (norm_nonneg _) (bilinear_le_sqrt_order_mul_collisions t r) 8
    _ = ((remainderCollisionCount t (addOrderOf r) : ℝ) ^ 8 *
        (addOrderOf r : ℝ) ^ 7) / (addOrderOf r : ℝ) ^ 3 := by
      rw [mul_pow, hsqrt]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hbound (by positivity)

/-- The fractional-power form directly matches a collision exceptional-set
threshold. The estimate is required only at divisors of the final modulus. -/
theorem eight_products_of_collision_rpow_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t : ι → ℕ)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (remainderCollisionCount t d : ℝ) ≤
        (Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8))
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι,
      ∑ i, (t (a i) : ZMod q) * (t (b i) : ZMod q) = target := by
  apply eight_products_of_collision_power_bound t _ target
  intro d hd hdq
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (remainderCollisionCount t d))
    (hcollision d hd hdq) 8
  have hexp : ((d : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 = (d : ℝ) ^ 7 := by
    rw [← Real.rpow_mul_natCast hdR.le]
    norm_num
  calc
    _ ≤ ((Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 *
        (d : ℝ) ^ 7 := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by
      rw [div_pow, hexp]
      field_simp

end Problem337.CompositeSpectral

end

end OAI
