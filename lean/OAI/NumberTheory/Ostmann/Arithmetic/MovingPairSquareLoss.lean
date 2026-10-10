import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeOccurrences
import OAI.NumberTheory.Ostmann.Arithmetic.JointSquareLiftExclusions

namespace OAI

/-! # Square-exclusion loss for both actual moving histories -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_on_fiber {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x₀ y₀ : ZMod p)
    (hbase : ∀ j : MovingPrimeOccurrences value T p,
      let φ := MovingSlotReversal.naturalReduction p value
      let L := movingPrimeOccurrenceLine value T p j
      φ L.a * x₀ + φ L.b * y₀ = 0)
    (v : SquareLiftPairs p x₀ y₀) :
    movingInternalPairFactor value T p v.1.1 v.2.1 =
      if ∀ j : MovingPrimeOccurrences value T p,
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        let L := movingPrimeOccurrenceLine value T p j
        φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 then 1 else 0 := by
  have hz (j : MovingPrimeOccurrences value T p) :
      let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
      let L := movingPrimeOccurrenceLine value T p j
      squareReduction p (φ L.a * v.1.1 + φ L.b * v.2.1) = 0 := by
    simpa only [map_add, map_mul, naturalReduction_square, v.1.property, v.2.property] using hbase j
  have hs : (∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1) ↔
      ∀ j : MovingPrimeOccurrences value T p,
        let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
        let L := movingPrimeOccurrenceLine value T p j
        φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 := by
    refine (movingInternalLocalSupport_occurrences value T p v.1.1 v.2.1).trans ?_
    exact ⟨fun h j => (h j).2, fun h j => ⟨hz j, h j⟩⟩
  by_cases h : ∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1
  · simp only [movingInternalPairFactor, ite_eq_left h, ite_eq_left (hs.mp h)]
  · have hn := fun hn => h (hs.mpr hn)
    simp only [movingInternalPairFactor, ite_eq_right h, ite_eq_right hn]

theorem moving_internal_pair_fiber_product {σ I : Type*} [Fintype I] {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : I → ℕ)
    (x₀ y₀ : ∀ i, ZMod (p i))
    (hbase : ∀ i (j : MovingPrimeOccurrences value T (p i)),
      let φ := MovingSlotReversal.naturalReduction (p i) value
      let L := movingPrimeOccurrenceLine value T (p i) j
      φ L.a * x₀ i + φ L.b * y₀ i = 0)
    (v : ∀ i, SquareLiftPairs (p i) (x₀ i) (y₀ i)) (w : ℂ) :
    (∏ i, movingInternalPairFactor value T (p i) (v i).1.1 (v i).2.1) * w =
      if ∀ i (j : MovingPrimeOccurrences value T (p i)),
        let φ := MovingSlotReversal.naturalReduction (p i ^ 2) value
        let L := movingPrimeOccurrenceLine value T (p i) j
        φ L.a * (v i).1.1 + φ L.b * (v i).2.1 ≠ 0 then w else 0 := by
  simp_rw [movingInternalPairFactor_on_fiber value T _ _ _ (hbase _)]
  by_cases h : ∀ i (j : MovingPrimeOccurrences value T (p i)),
      let φ := MovingSlotReversal.naturalReduction (p i ^ 2) value
      let L := movingPrimeOccurrenceLine value T (p i) j
      φ L.a * (v i).1.1 + φ L.b * (v i).2.1 ≠ 0
  · rw [ite_eq_left h]
    have he : (∏ i, if ∀ j : MovingPrimeOccurrences value T (p i),
        let φ := MovingSlotReversal.naturalReduction (p i ^ 2) value
        let L := movingPrimeOccurrenceLine value T (p i) j
        φ L.a * (v i).1.1 + φ L.b * (v i).2.1 ≠ 0 then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one (fun i _ => ite_eq_left (h i))
    rw [he, one_mul]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    have he : (∏ i, if ∀ j : MovingPrimeOccurrences value T (p i),
        let φ := MovingSlotReversal.naturalReduction (p i ^ 2) value
        let L := movingPrimeOccurrenceLine value T (p i) j
        φ L.a * (v i).1.1 + φ L.b * (v i).2.1 ≠ 0 then (1 : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    rw [he, zero_mul]

/-- The two-history loss counts each node once even if it contains several
copies of the same prime. All its nonzero-row assumptions are derived. -/
theorem moving_pair_joint_square_loss {σ I : Type*} [Fintype I] [DecidableEq I]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (hf : ∀ i side, (T side).Frequencies (fun s => (s : ZMod (p i)) ≠ 0))
    (x₀ y₀ : ∀ i, ZMod (p i)) (hy : ∀ i, y₀ i ≠ 0)
    (hbase : ∀ i (j : MovingPrimeOccurrences value T (p i)),
      let φ := MovingSlotReversal.naturalReduction (p i) value
      let L := movingPrimeOccurrenceLine value T (p i) j
      φ L.a * x₀ i + φ L.b * y₀ i = 0)
    (F : (∀ i, SquareLiftPairs (p i) (x₀ i) (y₀ i)) → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ v, ‖F v‖ ≤ B) :
    (Fintype.card (∀ i, SquareLiftPairs (p i) (x₀ i) (y₀ i)) : ℝ)⁻¹ *
      ‖(∑ v, (∏ i, movingInternalPairFactor value T (p i) (v i).1.1 (v i).2.1) * F v) -
        ∑ v, F v‖ ≤
      4 * B * (2 ^ n - 1 : ℕ) * ∑ i, (p i : ℝ)⁻¹ := by
  let J := fun i => MovingPrimeOccurrences value T (p i)
  let φ := fun i => MovingSlotReversal.naturalReduction (p i ^ 2) value
  let L := fun i (j : J i) => movingPrimeOccurrenceLine value T (p i) j
  have hr (i : I) (j : J i) :
      squareReduction (p i) (φ i (L i j).a) ≠ 0 ∨
        squareReduction (p i) (φ i (L i j).b) ≠ 0 := by
    simp only [φ, naturalReduction_square]
    exact movingPrimeOccurrenceLine_nonzero tier value hprime hdisjoint T hlevels (p i) (hf i) j
  have hb := joint_square_lift_removed_mass_le p J
    (fun i j => φ i (L i j).a) (fun i j => φ i (L i j).b) x₀ y₀ hy hr
    (by simpa only [φ, naturalReduction_square] using hbase) F B hB hF
  simp_rw [moving_internal_pair_fiber_product value T p x₀ y₀ hbase]
  refine hb.trans ?_
  calc
    2 * B * ∑ i, (Fintype.card (J i) : ℝ) / p i ≤
        2 * B * ∑ i, (2 * (2 ^ n - 1 : ℕ) : ℝ) / (p i : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast movingPrimeOccurrences_card value T (p i)
    _ = _ := by simp only [div_eq_mul_inv, ← Finset.mul_sum]; ring

end Ostmann

end OAI
