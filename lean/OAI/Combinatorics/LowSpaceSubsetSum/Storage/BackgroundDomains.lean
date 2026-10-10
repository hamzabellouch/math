import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundAllocation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

namespace OAI

/-! # A concrete ordered partition of the background indices -/

namespace LowSpaceSubsetSum

open scoped BigOperators

/-- Four children, each split into its two consecutive leaf parts. -/
def eightLeafCounts (a b c d : ℕ) : Fin 8 → ℕ :=
  ![leafBackgroundSize a 0, leafBackgroundSize a 1,
    leafBackgroundSize b 0, leafBackgroundSize b 1,
    leafBackgroundSize c 0, leafBackgroundSize c 1,
    leafBackgroundSize d 0, leafBackgroundSize d 1]

theorem eightLeafCounts_sum (a b c d : ℕ) :
    ∑ i, eightLeafCounts a b c d i = a + b + c + d := by
  simp only [eightLeafCounts, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  have ha := leafBackgroundSize_sum a
  have hb := leafBackgroundSize_sum b
  have hc := leafBackgroundSize_sum c
  have hd := leafBackgroundSize_sum d
  omega

/-- The exact two-level integer allocations in the implementation. -/
def computedLeafCounts (r a0 b0 aL bL aR bR : ℕ) : Fin 8 → ℕ :=
  let left := allocateLeft r a0 b0
  let right := allocateRight r a0 b0
  eightLeafCounts (allocateLeft left aL bL) (allocateRight left aL bL)
    (allocateLeft right aR bR) (allocateRight right aR bR)

theorem computedLeafCounts_sum (r a0 b0 aL bL aR bR : ℕ)
    (h0a : a0 ≤ r + b0) (h0b : b0 ≤ r + a0)
    (hLa : aL ≤ allocateLeft r a0 b0 + bL) (hLb : bL ≤ allocateLeft r a0 b0 + aL)
    (hRa : aR ≤ allocateRight r a0 b0 + bR) (hRb : bR ≤ allocateRight r a0 b0 + aR) :
    ∑ i, computedLeafCounts r a0 b0 aL bL aR bR i = r := by
  have h0 := (allocation_feasible r a0 b0 h0a h0b).2
  have hL := (allocation_feasible (allocateLeft r a0 b0) aL bL hLa hLb).2
  have hR := (allocation_feasible (allocateRight r a0 b0) aR bR hRa hRb).2
  rw [computedLeafCounts, eightLeafCounts_sum]
  omega

/-- Successive blocks in the sorted outside domain, with the prescribed eight
sizes. The library equivalence uses prefix sums of these sizes. -/
def backgroundIndexEquiv {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) : ↥V ≃ ((i : Fin 8) × Fin (c i)) :=
  (V.orderIsoOfFin rfl).toEquiv.symm.trans ((finCongr hc.symm).trans finSigmaFinEquiv.symm)

def backgroundColor {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) (x : Fin n) : Fin 8 :=
  if hx : x ∈ V then (backgroundIndexEquiv V c hc ⟨x, hx⟩).1 else 0

theorem backgroundColor_card {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) (j : Fin 8) :
    (V.filter fun x => backgroundColor V c hc x = j).card = c j := by
  classical
  let e := backgroundIndexEquiv V c hc
  let f : Fin (c j) → Fin n := fun k => (e.symm ⟨j, k⟩).val
  have hf : Function.Injective f := by
    intro x y h
    have hsub : e.symm ⟨j, x⟩ = e.symm ⟨j, y⟩ := Subtype.ext h
    have hs := e.symm.injective hsub
    exact sigma_mk_injective (β := fun i : Fin 8 => Fin (c i)) hs
  have heq : (V.filter fun x => backgroundColor V c hc x = j) = Finset.univ.image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxV, hxC⟩ := Finset.mem_filter.mp hx
      let v : ↥V := ⟨x, hxV⟩
      have hxE : (e v).1 = j := by simpa only [backgroundColor, dite_eq_left hxV] using hxC
      rcases hev : e v with ⟨k, y⟩
      have hkj : k = j := by simpa only [hev] using hxE
      subst k
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_univ _, ?_⟩
      change (e.symm ⟨j, y⟩).val = x
      rw [← hev, e.symm_apply_apply]
    · intro hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      have hV := (e.symm ⟨j, k⟩).property
      apply Finset.mem_filter.mpr
      refine ⟨hV, ?_⟩
      simp only [backgroundColor, f, dite_eq_left hV]
      exact congrArg Sigma.fst (e.apply_symm_apply ⟨j, k⟩)
  rw [heq, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

/-- The eight linear labels are the two parents and four leaves of the table. -/
def backgroundPairColor {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) (x : Fin n) : Fin 2 × Fin 4 :=
  let j := backgroundColor V c hc x
  (⟨j.val / 4, by omega⟩, ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩)


theorem backgroundPairColor_eq_iff {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) (x : Fin n) (j : Fin 2) (i : Fin 4) :
    backgroundPairColor V c hc x = (j, i) ↔
      backgroundColor V c hc x = ⟨4 * j.val + i.val, by omega⟩ := by
  simp only [backgroundPairColor, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro ⟨h0, h1⟩
    omega
  · intro h
    constructor <;> omega

theorem backgroundPairColor_card {n : ℕ} (V : Finset (Fin n)) (c : Fin 8 → ℕ)
    (hc : ∑ i, c i = V.card) (j : Fin 2) (i : Fin 4) :
    (V.filter fun x => backgroundPairColor V c hc x = (j, i)).card =
      c ⟨4 * j.val + i.val, by omega⟩ := by
  simp_rw [backgroundPairColor_eq_iff]
  exact backgroundColor_card V c hc _

end LowSpaceSubsetSum

end OAI
