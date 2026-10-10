import OAI.Combinatorics.DiscreteConvexity.CoveringBasic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# The total weight of residual tuples

We bound the sum over injective edge tuples by the sum over all edge tuples.
Splitting an unrestricted tuple into its first edge and its tail gives an
exact weighted recurrence. The per-union extension bound then controls every
step. No nonemptiness assumption on the edge family is needed.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable section

/-- The union of an unrestricted ordered edge tuple. -/
def allTupleUnion {H : Family V} {t : ℕ} (f : Fin t → ↥H) : Finset V :=
  Finset.univ.biUnion (fun i => (f i).val)

/-- Weight of the union of an injective tuple. -/
def tupleWeight {H : Family V} {t : ℕ} (rho : ℝ) (f : EdgeTuple H t) : ℝ :=
  rho ^ (tupleUnion f).card

def tupleWeightSum (H : Family V) (rho : ℝ) (t : ℕ) : ℝ :=
  ∑ f : EdgeTuple H t, tupleWeight rho f

/-- The larger sum in which repeated edges are allowed. -/
def allTupleWeightSum (H : Family V) (rho : ℝ) (t : ℕ) : ℝ :=
  ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card

theorem tupleWeight_nonneg {H : Family V} {t : ℕ} {rho : ℝ}
    (hrho : 0 ≤ rho) (f : EdgeTuple H t) : 0 ≤ tupleWeight rho f :=
  pow_nonneg hrho _

@[simp] theorem allTupleUnion_zero {H : Family V} (f : Fin 0 → ↥H) :
    allTupleUnion f = ∅ := by
  simp [allTupleUnion]

@[simp] theorem allTupleWeightSum_zero (H : Family V) (rho : ℝ) :
    allTupleWeightSum H rho 0 = 1 := by
  classical
  simp [allTupleWeightSum]

@[simp] theorem tupleWeightSum_zero (H : Family V) (rho : ℝ) :
    tupleWeightSum H rho 0 = 1 := by
  classical
  let : Unique (EdgeTuple H 0) :=
    { default := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      uniq := fun f => Subtype.ext (funext fun i => Fin.elim0 i) }
  simp [tupleWeightSum, tupleWeight, tupleUnion]

/-- An unrestricted `t`-tuple of `r`-element edges uses at most `r * t` vertices. -/
theorem allTupleUnion_card_le {H : Family V} {r t : ℕ}
    (uniform : ∀ e ∈ H, (e : Finset V).card = r) (f : Fin t → ↥H) :
    (allTupleUnion f).card ≤ r * t := by
  classical
  calc
    (allTupleUnion f).card ≤ ∑ i : Fin t, (f i).val.card :=
      Finset.card_biUnion_le
    _ = ∑ _i : Fin t, r :=
      Finset.sum_congr rfl (fun i _ => uniform (f i).val (f i).property)
    _ = r * t := by simp [Nat.mul_comm]

theorem tupleUnion_card_le {H : Family V} {r t : ℕ}
    (uniform : ∀ e ∈ H, (e : Finset V).card = r) (f : EdgeTuple H t) :
    (tupleUnion f).card ≤ r * t :=
  allTupleUnion_card_le uniform f.val

/-- Splitting a tuple separates its old union from the newly chosen edge. -/
theorem allTupleUnion_cons {H : Family V} {t : ℕ}
    (e : ↥H) (f : Fin t → ↥H) :
    allTupleUnion (Fin.cons e f) = allTupleUnion f ∪ e.val := by
  ext v
  simp [allTupleUnion, Fin.exists_fin_succ, or_comm]

/-- Union weight factors exactly into the prefix weight and its extension cost. -/
theorem allTupleWeight_cons {H : Family V} {t : ℕ} (rho : ℝ)
    (e : ↥H) (f : Fin t → ↥H) :
    rho ^ (allTupleUnion (Fin.cons e f)).card =
      rho ^ (allTupleUnion f).card * rho ^ (e.val \ allTupleUnion f).card := by
  rw [allTupleUnion_cons, Finset.union_comm,
    ← Finset.card_sdiff_add_card, pow_add, mul_comm]

/-- Exact recurrence for the unrestricted sum, obtained by reindexing with `Fin.cons`. -/
theorem allTupleWeightSum_succ (H : Family V) (rho : ℝ) (t : ℕ) :
    allTupleWeightSum H rho (t + 1) =
      ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card *
        (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) := by
  classical
  calc
    allTupleWeightSum H rho (t + 1) =
        ∑ p : ↥H × (Fin t → ↥H),
          rho ^ (allTupleUnion (Fin.cons p.1 p.2)).card := by
      exact ((Fin.consEquiv (fun _ : Fin (t + 1) => ↥H)).sum_comp
        (fun f => rho ^ (allTupleUnion f).card)).symm
    _ = ∑ f : Fin t → ↥H, ∑ e : ↥H,
        rho ^ (allTupleUnion (Fin.cons e f)).card :=
      Fintype.sum_prod_type_right _
    _ = ∑ f : Fin t → ↥H, rho ^ (allTupleUnion f).card *
        (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) := by
      apply Finset.sum_congr rfl
      intro f _
      simp_rw [allTupleWeight_cons]
      rw [← Finset.mul_sum, Finset.sum_coe_sort H
        (fun e : Finset V => rho ^ (e \ allTupleUnion f).card)]

/-- Discarding the injectivity restriction increases the sum of nonnegative weights. -/
theorem tupleWeightSum_le_allTupleWeightSum (H : Family V) {rho : ℝ}
    (hrho : 0 ≤ rho) (t : ℕ) :
    tupleWeightSum H rho t ≤ allTupleWeightSum H rho t := by
  classical
  calc
    tupleWeightSum H rho t =
        ∑ f ∈ Finset.univ.filter (fun f : Fin t → ↥H => Function.Injective f),
          rho ^ (allTupleUnion f).card := by
      exact (Finset.sum_subtype
        (p := fun f : Fin t → ↥H => Function.Injective f)
        (Finset.univ.filter (fun f : Fin t → ↥H => Function.Injective f))
        (fun f => by simp) (fun f => rho ^ (allTupleUnion f).card)).symm
    _ ≤ allTupleWeightSum H rho t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f _ _ => pow_nonneg hrho _)

/-- The extension estimate yields the unrestricted recurrence up to a fixed length. -/
theorem allTupleWeightSum_succ_le (H : Family V) {rho T : ℝ} {r m t : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (ht : t ≤ m) :
    allTupleWeightSum H rho (t + 1) ≤
      (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) * allTupleWeightSum H rho t := by
  classical
  rw [allTupleWeightSum_succ, allTupleWeightSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have hcard : (allTupleUnion f).card ≤ r * m :=
    (allTupleUnion_card_le uniform f).trans (Nat.mul_le_mul_left r ht)
  have hcast : ((allTupleUnion f).card : ℝ) ≤ ((r * m : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcard
  have hpower : (1 + ((allTupleUnion f).card : ℝ)) ^ r ≤
      (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (Nat.cast_nonneg _))
      (add_le_add (le_refl (1 : ℝ)) hcast) r
  have hext : (∑ e ∈ H, rho ^ (e \ allTupleUnion f).card) ≤
      T * (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    (extension (allTupleUnion f)).trans (mul_le_mul_of_nonneg_left hpower hT)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hext (pow_nonneg hrho (allTupleUnion f).card)

/-- Iteration of the actual recurrence bounds every unrestricted sum up to `m`. -/
theorem allTupleWeightSum_le (H : Family V) {rho T : ℝ} {r m : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (t : ℕ) (ht : t ≤ m) :
    allTupleWeightSum H rho t ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ t := by
  have hfactor : 0 ≤ T * (1 + ((r * m : ℕ) : ℝ)) ^ r :=
    mul_nonneg hT (pow_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) r)
  revert ht
  induction t with
  | zero => intro ht; simp
  | succ t ih =>
      intro ht
      have htm : t ≤ m := Nat.le_of_succ_le ht
      calc
        allTupleWeightSum H rho (t + 1) ≤
            (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) * allTupleWeightSum H rho t :=
          allTupleWeightSum_succ_le H hrho hT uniform extension htm
        _ ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) *
            (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ t :=
          mul_le_mul_of_nonneg_left (ih htm) hfactor
        _ = (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ (t + 1) := by
          rw [pow_succ, mul_comm]

theorem tupleWeightSum_le (H : Family V) {rho T : ℝ} {r m : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r) :
    tupleWeightSum H rho m ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ m :=
  (tupleWeightSum_le_allTupleWeightSum H hrho m).trans
    (allTupleWeightSum_le H hrho hT uniform extension m le_rfl)

end

end TalagrandDiscreteConvexity.Covering

end OAI
