import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelFrozen
import OAI.NumberTheory.Ostmann.Arithmetic.BulkFrequencyFactor
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotFieldBridge
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSpectatorNorm

namespace OAI

/-! # The frequency core under the original independent bulk-slot law -/

namespace Ostmann
open scoped Classical BigOperators

theorem treeIntegerResidues_of_naturalLift {Q : ℕ} (n : ℕ)
    (a : TreeLeafTuple ℕ n) (z : TreeLeafTuple (ZMod Q)ˣ n)
    (h : TreeNaturalLift n a z) :
    treeIntegerResidues Q n (treeLeafMap (fun q : ℕ => (q : ℤ)) n a) z := by
  induction n with
  | zero => simpa only [treeIntegerResidues, treeLeafMap, Int.cast_natCast] using h.symm
  | succ n ih => exact ⟨ih a.1 z.1 h.1, ih a.2 z.2 h.2⟩

theorem bulkUnitRepresentative_coprime {σ J : Type*} (base : σ → ℕ) (slot : J ↪ σ)
    (R Q : ℕ) [NeZero Q] (hRQ : R ∣ Q)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (z : J → (ZMod Q)ˣ) (i : σ) :
    IsCoprime ((Function.extend slot (fun j => (z j).val.val) base i : ℕ) : ℤ) (R : ℤ) := by
  by_cases hi : ∃ j, slot j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [slot.injective.extend_apply]
    have hc : IsCoprime ((z j).val.val : ℤ) (Q : ℤ) := by
      apply IsCoprime.symm
      apply (ZMod.coe_int_isUnit_iff_isCoprime _ Q).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using (z j).isUnit
    exact hc.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hRQ)
  · rw [Function.extend_apply' _ base i hi]
    exact hbase i hi

/-- Keep the support indicator while taking the norm of the actual core.
The adaptive data uses the fixed nonbulk values; only the bulk law varies. -/
theorem frequencyModelBulkCore_norm_support {σ : Type*}
    (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
    [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
    (slot : (TreeLeafIndex n × Fin m) ↪ σ)
    (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
    (hslot : ∀ j, n ≤ tier (slot j))
    (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
    (ha : ∀ b, (a b).Levels tier)
    (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
    (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
    (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
    (x y : ℤ) (z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) :
    let value := Function.extend slot (fun j => (z j).val.val) base
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    let Z := (treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z)
    ‖movingFrequencyCore value F E T R x y‖ ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      arithmeticLeafSupport n (frequencyModelPairData base S n R t hS hR small a x y) Z := by
  intro value T Z
  have hfixed (b : Bool) := frozenMoving_nonbulk_values tier base value slot n hslot
    (fun i hi => Function.extend_apply' _ base i hi) (small b) (a b) (hsmall b) (ha b)
  have hdata := frequencyModelPairData_congr value base S n R t hS hR small a x y
    (fun b => (hfixed b).1) (fun b => (hfixed b).2)
  have hunit := bulkUnitRepresentative_coprime base slot R (R ^ (n - 1 + 2))
    (dvd_pow_self R (by omega)) hbase z
  have hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n (bulkSlotLeaves n m slot))) Z :=
    treeIntegerResidues_of_naturalLift n _ _ (bulkSlotLeaves_naturalLift value n m slot z
      (fun j => by
        change ((Function.extend slot (fun j => (z j).val.val) base (slot j) : ℕ) : ZMod (R ^ (n - 1 + 2))) = _
        rw [slot.injective.extend_apply, ZMod.natCast_zmod_val]))
  by_cases hg : ∀ b, movingFrequencyGate value R (T b) x y
  · have hs := frequencyModelPairData_support value S n R t hS hR small
      (bulkSlotLeaves n m slot) a x y hunit Z hz hg
    rw [hdata] at hs
    rw [hs, mul_one]
    rw [movingFrequencyCore, ite_eq_left hg, norm_mul, Complex.norm_conj]
  · rw [movingFrequencyCore, ite_eq_right hg, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (arithmeticLeafSupport_nonneg n _ Z)

/-- Passing from individual bulk slots to their leaf products is an exact
uniform averaging identity. -/
theorem arithmeticLeafSupport_bulk_average {Q : ℕ} [NeZero Q] (n m : ℕ) (hm : 0 < m)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod Q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod Q)ˣ, arithmeticLeafSupport n data
        ((treeLeafTupleEquiv (ZMod Q)ˣ n).symm (bulkBlockProduct z))) =
      (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        ∑ z : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n data z := by
  have h := bulkBlockProduct_average (L := TreeLeafIndex n) (G := (ZMod Q)ˣ) (m := m) hm
    (fun z => arithmeticLeafSupport n data ((treeLeafTupleEquiv (ZMod Q)ˣ n).symm z))
  let e := treeLeafTupleEquiv (ZMod Q)ˣ n
  have he := e.symm.sum_comp (arithmeticLeafSupport n data)
  have hc := Fintype.card_congr e
  simp only [finite_univ_canonical, Fintype.card_eq_nat_card] at h he hc ⊢
  rw [← hc, he] at h
  exact h

end Ostmann

end OAI
